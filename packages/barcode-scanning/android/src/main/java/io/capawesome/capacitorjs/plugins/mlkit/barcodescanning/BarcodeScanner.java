package io.capawesome.capacitorjs.plugins.mlkit.barcodescanning;

import android.annotation.SuppressLint;
import android.content.Intent;
import android.content.pm.PackageManager;
import android.graphics.Color;
import android.graphics.Point;
import android.graphics.Rect;
import android.media.Image;
import android.net.Uri;
import android.os.Build;
import android.provider.Settings;
import android.view.ViewGroup;
import android.widget.FrameLayout;

import androidx.annotation.NonNull;
import androidx.annotation.Nullable;
import androidx.camera.core.*;
import androidx.camera.lifecycle.ProcessCameraProvider;
import androidx.camera.view.PreviewView;
import androidx.core.content.ContextCompat;
import androidx.lifecycle.LifecycleOwner;

import com.getcapacitor.PermissionState;
import com.getcapacitor.PluginCall;
import com.google.android.gms.common.moduleinstall.InstallStatusListener;
import com.google.android.gms.common.moduleinstall.ModuleInstall;
import com.google.android.gms.common.moduleinstall.ModuleInstallClient;
import com.google.android.gms.common.moduleinstall.ModuleInstallRequest;
import com.google.android.gms.common.moduleinstall.ModuleInstallStatusUpdate;
import com.google.common.util.concurrent.ListenableFuture;
import com.google.mlkit.vision.barcode.BarcodeScannerOptions;
import com.google.mlkit.vision.barcode.BarcodeScanning;
import com.google.mlkit.vision.barcode.common.Barcode;
import com.google.mlkit.vision.codescanner.GmsBarcodeScanner;
import com.google.mlkit.vision.codescanner.GmsBarcodeScannerOptions;
import com.google.mlkit.vision.codescanner.GmsBarcodeScanning;
import com.google.mlkit.vision.common.InputImage;

import java.util.*;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;

import io.capawesome.capacitorjs.plugins.mlkit.barcodescanning.classes.options.SetZoomRatioOptions;
import io.capawesome.capacitorjs.plugins.mlkit.barcodescanning.classes.results.GetMaxZoomRatioResult;
import io.capawesome.capacitorjs.plugins.mlkit.barcodescanning.classes.results.GetMinZoomRatioResult;
import io.capawesome.capacitorjs.plugins.mlkit.barcodescanning.classes.results.GetZoomRatioResult;

public class BarcodeScanner implements ImageAnalysis.Analyzer {

    @Nullable
    private static Camera camera;

    @NonNull
    private final BarcodeScannerPlugin plugin;

    @Nullable
    private com.google.mlkit.vision.barcode.BarcodeScanner barcodeScannerInstance;

    @Nullable
    private ProcessCameraProvider processCameraProvider;

    @Nullable
    private PreviewView previewView;

    @Nullable
    private ScanSettings scanSettings;

    private final ExecutorService cameraExecutor = Executors.newSingleThreadExecutor();

    private final HashMap<String, Integer> barcodeRawValueVotes = new HashMap<>();
    private enum ZoomMode {
        NONE,
        ZOOM_IN,
        ZOOM_OUT
    }
    private boolean isTorchEnabled = false;
    private boolean isPaused = false;

    private long lastAnalyzedTime = 0;
    private static final long ANALYZE_INTERVAL_MS = 150; // ~6 FPS
    // ================= AUTO ZOOM =================
    private ZoomMode zoomMode = ZoomMode.NONE;

    private long lastZoomUpdateTime = 0;
    private static final long ZOOM_COOLDOWN_MS = 350;
    private static final float ZOOM_LERP_FACTOR = 0.15f;

    // hard thresholds
    private static final float QR_TOO_SMALL = 0.18f;
    private static final float QR_TOO_BIG   = 0.45f;

    private static final float QR_IDEAL_MIN = 0.25f;
    private static final float QR_IDEAL_MAX = 0.38f;

    private float lastAppliedZoom = -1f;
    private long lastBarcodeSeenTime = 0;

    private static final long AUTO_ZOOM_RESET_MS = 800;
    private static final float MIN_ZOOM_DELTA = 0.02f;
    // ===== QR TRACKING =====
    private static final float TRACKING_EASING = 0.25f;
    private static final float TRACKING_DEAD_ZONE = 0.08f; // 8% от центра

    private float lastFocusX = 0.5f;
    private float lastFocusY = 0.5f;

    private long lastTrackingTime = 0;
    private static final long TRACKING_COOLDOWN_MS = 250;

    public BarcodeScanner(BarcodeScannerPlugin plugin) {
        this.plugin = plugin;
    }

    // ================= START SCAN =================
    public void scan(
            ScanSettings scanSettings,
            ScanResultCallback callback
    ) {
        try {
            GmsBarcodeScannerOptions options = buildGmsBarcodeScannerOptions(scanSettings);

            GmsBarcodeScanner scanner =
                    GmsBarcodeScanning.getClient(plugin.getContext(), options);

            scanner
                    .startScan()
                    .addOnSuccessListener(callback::success)
                    .addOnCanceledListener(callback::cancel)
                    .addOnFailureListener(callback::error);

        } catch (Exception exception) {
            callback.error(exception);
        }
    }

    private void handleQrTracking(@NonNull Barcode barcode, @NonNull Point imageSize) {
        if (camera == null) return;

        Rect box = barcode.getBoundingBox();
        if (box == null) return;

        ZoomState zoomState = camera.getCameraInfo().getZoomState().getValue();
        if (zoomState == null) return;

        float qrX = box.centerX() / (float) imageSize.x;
        float dx = qrX - 0.5f;

        // dead zone
        if (Math.abs(dx) < 0.12f) return;

        float currentZoom = zoomState.getZoomRatio();
        float maxZoom = zoomState.getMaxZoomRatio();

        // tracking strength
        float trackingZoomBoost = Math.abs(dx) * 0.6f;

        float targetZoom = Math.min(
                currentZoom + trackingZoomBoost,
                maxZoom
        );

        float easedZoom =
                currentZoom + (targetZoom - currentZoom) * 0.2f;

        camera.getCameraControl().setZoomRatio(easedZoom);
    }
    private float clamp(float v, float min, float max) {
        return Math.max(min, Math.min(max, v));
    }

    // ================= AUTO ZOOM LOGIC =================

    private void handleAutoZoom(@NonNull Barcode barcode, @NonNull Point imageSize) {
        if (camera == null) return;

        Rect box = barcode.getBoundingBox();
        if (box == null) return;

        ZoomState zoomState = camera.getCameraInfo().getZoomState().getValue();
        if (zoomState == null) return;

        long now = System.currentTimeMillis();
        lastBarcodeSeenTime = now;

        if (now - lastZoomUpdateTime < ZOOM_COOLDOWN_MS) return;

        // === NORMALIZED QR SIZE (robust) ===
        float qrWidthNorm = (float) box.width() / imageSize.x;
        float qrHeightNorm = (float) box.height() / imageSize.y;
        float ratio = Math.max(qrWidthNorm, qrHeightNorm); // стабильнее, чем area

        float currentZoom = zoomState.getZoomRatio();
        float minZoom = zoomState.getMinZoomRatio();
        float maxZoom = zoomState.getMaxZoomRatio();

        // === hysteresis FSM ===
        switch (zoomMode) {
            case NONE:
                if (ratio < QR_TOO_SMALL) {
                    zoomMode = ZoomMode.ZOOM_IN;
                } else if (ratio > QR_TOO_BIG) {
                    zoomMode = ZoomMode.ZOOM_OUT;
                } else {
                    return;
                }
                break;

            case ZOOM_IN:
                if (ratio >= QR_IDEAL_MIN) {
                    zoomMode = ZoomMode.NONE;
                    return;
                }
                break;

            case ZOOM_OUT:
                if (ratio <= QR_IDEAL_MAX) {
                    zoomMode = ZoomMode.NONE;
                    return;
                }
                break;
        }

        float targetZoom = currentZoom;

        if (zoomMode == ZoomMode.ZOOM_IN) {
            targetZoom = Math.min(currentZoom + 0.7f, maxZoom);
        } else if (zoomMode == ZoomMode.ZOOM_OUT) {
            targetZoom = Math.max(currentZoom - 0.7f, minZoom);
        }

        float easedZoom =
                currentZoom + (targetZoom - currentZoom) * ZOOM_LERP_FACTOR;

        // === anti-jitter ===
        if (lastAppliedZoom > 0 &&
                Math.abs(easedZoom - lastAppliedZoom) < MIN_ZOOM_DELTA) {
            return;
        }

        plugin.getActivity().runOnUiThread(() ->
                camera.getCameraControl().setZoomRatio(easedZoom)
        );

        lastAppliedZoom = easedZoom;
        lastZoomUpdateTime = now;
    }

    private GmsBarcodeScannerOptions buildGmsBarcodeScannerOptions(
            ScanSettings scanSettings
    ) {
        int[] formats =
                scanSettings.formats.length == 0
                        ? new int[]{Barcode.FORMAT_ALL_FORMATS}
                        : scanSettings.formats;

        GmsBarcodeScannerOptions.Builder builder =
                new GmsBarcodeScannerOptions.Builder()
                        .setBarcodeFormats(formats[0], formats);

        if (scanSettings.autoZoom) {
            builder.enableAutoZoom();
        }

        return builder.build();
    }


    public boolean isSupported() {
        return plugin.getContext().getPackageManager().hasSystemFeature(PackageManager.FEATURE_CAMERA_ANY);
    }

    public void enableTorch() {
        if (camera == null) {
            return;
        }
        camera.getCameraControl().enableTorch(true);
        isTorchEnabled = true;
    }

    public void toggleTorch() {
        if (isTorchEnabled) {
            disableTorch();
        } else {
            enableTorch();
        }
    }

    public boolean isTorchEnabled() {
        return isTorchEnabled;
    }

    public boolean isTorchAvailable() {
        return plugin.getContext().getPackageManager().hasSystemFeature(PackageManager.FEATURE_CAMERA_FLASH);
    }

    public void startScan(ScanSettings scanSettings, StartScanResultCallback callback) {
        stopScan();
        hideWebViewBackground();

        this.scanSettings = scanSettings;

        barcodeScannerInstance = BarcodeScanning.getClient(buildBarcodeScannerOptions(scanSettings));

        ImageAnalysis imageAnalysis = new ImageAnalysis.Builder()
                .setBackpressureStrategy(ImageAnalysis.STRATEGY_KEEP_ONLY_LATEST)
                .setTargetAspectRatio(AspectRatio.RATIO_16_9)
                .setOutputImageFormat(ImageAnalysis.OUTPUT_IMAGE_FORMAT_YUV_420_888)
                .build();

        imageAnalysis.setAnalyzer(cameraExecutor, this);

        ListenableFuture<ProcessCameraProvider> future =
                ProcessCameraProvider.getInstance(plugin.getContext());

        future.addListener(() -> {
            try {
                processCameraProvider = future.get();

                CameraSelector cameraSelector =
                        new CameraSelector.Builder()
                                .requireLensFacing(scanSettings.lensFacing)
                                .build();

                previewView = new PreviewView(plugin.getActivity());
                previewView.setLayoutParams(new FrameLayout.LayoutParams(
                        FrameLayout.LayoutParams.MATCH_PARENT,
                        FrameLayout.LayoutParams.MATCH_PARENT
                ));
                previewView.setBackgroundColor(Color.BLACK);

                ((ViewGroup) plugin.getBridge().getWebView().getParent())
                        .addView(previewView, 0);

                Preview preview = new Preview.Builder().build();
                preview.setSurfaceProvider(previewView.getSurfaceProvider());

                camera = processCameraProvider.bindToLifecycle(
                        (LifecycleOwner) plugin.getContext(),
                        cameraSelector,
                        preview,
                        imageAnalysis
                );

                callback.success();
            } catch (Exception e) {
                callback.error(e);
            }
        }, ContextCompat.getMainExecutor(plugin.getContext()));
    }

    /**
     * Must run on UI thread.
     */
    public void resumeScan() {
        if (!isPaused || scanSettings == null || processCameraProvider == null) {
            return;
        }

        isPaused = false;

        try {
            ImageAnalysis imageAnalysis = new ImageAnalysis.Builder()
                    .setBackpressureStrategy(ImageAnalysis.STRATEGY_KEEP_ONLY_LATEST)
                    .setTargetAspectRatio(AspectRatio.RATIO_16_9)
                    .setOutputImageFormat(ImageAnalysis.OUTPUT_IMAGE_FORMAT_YUV_420_888)
                    .build();

            imageAnalysis.setAnalyzer(cameraExecutor, this);

            CameraSelector cameraSelector =
                    new CameraSelector.Builder()
                            .requireLensFacing(scanSettings.lensFacing)
                            .build();

            Preview preview = new Preview.Builder().build();
            if (previewView != null) {
                preview.setSurfaceProvider(previewView.getSurfaceProvider());
            }

            camera = processCameraProvider.bindToLifecycle(
                    (LifecycleOwner) plugin.getContext(),
                    cameraSelector,
                    preview,
                    imageAnalysis
            );

            if (isTorchEnabled && camera != null) {
                camera.getCameraControl().enableTorch(true);
            }
        } catch (Exception exception) {
            handleScanError(exception);
        }
    }

    public void isGoogleBarcodeScannerModuleAvailable(
            IsGoogleBarodeScannerModuleAvailableResultCallback callback
    ) {
        try {
            GmsBarcodeScanner scanner =
                    GmsBarcodeScanning.getClient(plugin.getContext());

            ModuleInstallClient moduleInstallClient =
                    ModuleInstall.getClient(plugin.getContext());

            moduleInstallClient
                    .areModulesAvailable(scanner)
                    .addOnSuccessListener(response -> {
                        callback.success(response.areModulesAvailable());
                    })
                    .addOnFailureListener(callback::error);
        } catch (Exception exception) {
            callback.error(exception);
        }
    }


    public void readBarcodesFromImage(
            String path,
            ScanSettings scanSettings,
            ReadBarcodesFromImageResultCallback callback
    ) throws Exception {

        InputImage inputImage;
        try {
            inputImage = InputImage.fromFilePath(
                    plugin.getContext(),
                    Uri.parse(path)
            );
        } catch (Exception exception) {
            throw new Exception(BarcodeScannerPlugin.ERROR_LOAD_IMAGE_FAILED);
        }

        BarcodeScannerOptions options = buildBarcodeScannerOptions(scanSettings);
        com.google.mlkit.vision.barcode.BarcodeScanner scanner =
                BarcodeScanning.getClient(options);

        scanner
                .process(inputImage)
                .addOnSuccessListener(callback::success)
                .addOnFailureListener(callback::error);
    }

    private void handleScanError(Exception exception) {
        if (exception == null) {
            return;
        }
        plugin.notifyScanErrorListener(exception.getMessage());
    }

    // ================= ANALYZE =================

    @Override
    public void analyze(@NonNull ImageProxy imageProxy) {
        if (isPaused || barcodeScannerInstance == null) {
            imageProxy.close();
            return;
        }

        @SuppressLint("UnsafeOptInUsageError")
        Image image = imageProxy.getImage();
        if (image == null) {
            imageProxy.close();
            return;
        }

        InputImage inputImage = InputImage.fromMediaImage(
                image,
                imageProxy.getImageInfo().getRotationDegrees()
        );

        Point imageSize = new Point(inputImage.getWidth(), inputImage.getHeight());

        barcodeScannerInstance
                .process(inputImage)
                .addOnSuccessListener(barcodes -> {
                    if (scanSettings == null) return;

                    List<Barcode> accepted = voteForBarcodes(barcodes);
                    if (accepted.isEmpty()) {
                        long now = System.currentTimeMillis();

                        if (scanSettings.autoZoom &&
                                zoomMode != ZoomMode.NONE &&
                                now - lastBarcodeSeenTime > AUTO_ZOOM_RESET_MS) {

                            zoomMode = ZoomMode.ZOOM_OUT;
                            lastBarcodeSeenTime = now;
                        }
                        return;
                    }

                    if (!accepted.isEmpty()) {

                        if (scanSettings.autoZoom) {
                            handleAutoZoom(accepted.get(0), imageSize);
                            handleQrTracking(accepted.get(0), imageSize);
                        }

                        handleScannedBarcodes(
                                accepted.toArray(new Barcode[0]),
                                imageSize
                        );
                    }
                })
                .addOnCompleteListener(task -> imageProxy.close());
    }
    // ================= VOTING =================

    private List<Barcode> voteForBarcodes(List<Barcode> barcodes) {
        List<Barcode> result = new ArrayList<>();
        for (Barcode barcode : barcodes) {
            String raw = barcode.getRawValue();
            if (raw == null) continue;

            int votes = 0;
            if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.N) {
                votes = barcodeRawValueVotes.getOrDefault(raw, 0) + 1;
            }
            barcodeRawValueVotes.put(raw, votes);

            if (votes >= 3) {
                result.add(barcode);
            }
        }
        return result;
    }



    // ================= STOP / PAUSE =================

    public void stopScan() {
        showWebViewBackground();
        disableTorch();

        if (processCameraProvider != null) {
            processCameraProvider.unbindAll();
        }

        processCameraProvider = null;
        camera = null;

        if (previewView != null) {
            ((ViewGroup) previewView.getParent()).removeView(previewView);
            previewView = null;
        }

        barcodeScannerInstance = null;
        scanSettings = null;
        barcodeRawValueVotes.clear();
        isPaused = false;
    }

    public void pauseScan() {
        isPaused = true;
        if (processCameraProvider != null) {
            processCameraProvider.unbindAll();
        }
    }

    // ================= OPTIONS =================

    private BarcodeScannerOptions buildBarcodeScannerOptions(ScanSettings scanSettings) {
        int[] formats =
                scanSettings.formats.length == 0
                        ? new int[]{Barcode.FORMAT_QR_CODE}
                        : scanSettings.formats;

        return new BarcodeScannerOptions.Builder()
                .setBarcodeFormats(formats[0], formats)
                .build();
    }


    public void openSettings(PluginCall call) {
        Uri uri = Uri.fromParts("package", plugin.getAppId(), null);
        Intent intent = new Intent(Settings.ACTION_APPLICATION_DETAILS_SETTINGS, uri);
        plugin.startActivityForResult(call, intent, "openSettingsResult");
    }

    public void installGoogleBarcodeScannerModule(InstallGoogleBarcodeScannerModuleResultCallback callback) {
        GmsBarcodeScanner scanner = GmsBarcodeScanning.getClient(plugin.getContext());
        InstallStatusListener listener = new ModuleInstallProgressListener(this);
        ModuleInstallRequest moduleInstallRequest = ModuleInstallRequest.newBuilder().addApi(scanner).setListener(listener).build();
        ModuleInstallClient moduleInstallClient = ModuleInstall.getClient(plugin.getContext());
        moduleInstallClient
                .installModules(moduleInstallRequest)
                .addOnSuccessListener(moduleInstallResponse -> {
                    if (moduleInstallResponse.areModulesAlreadyInstalled()) {
                        callback.error(new Exception(BarcodeScannerPlugin.ERROR_GOOGLE_BARCODE_SCANNER_MODULE_ALREADY_INSTALLED));
                    } else {
                        callback.success();
                    }
                })
                .addOnFailureListener(exception -> {
                    callback.error(exception);
                });
    }

    public boolean isCameraActive() {
        return camera != null;
    }
    // ================= HELPERS =================

    private void hideWebViewBackground() {
        plugin.getBridge().getWebView().setBackgroundColor(Color.TRANSPARENT);
    }

    private void showWebViewBackground() {
        plugin.getBridge().getWebView().setBackgroundColor(Color.WHITE);
    }

    private void handleScannedBarcodes(Barcode[] barcodes, Point imageSize) {
        plugin.notifyBarcodesScannedListener(barcodes, imageSize);
    }

    @Nullable
    public GetZoomRatioResult getZoomRatio() {
        if (camera == null) {
            return null;
        }
        float zoomRatio = camera.getCameraInfo().getZoomState().getValue().getZoomRatio();
        return new GetZoomRatioResult(zoomRatio);
    }

    @Nullable
    public GetMinZoomRatioResult getMinZoomRatio() {
        if (camera == null) {
            return null;
        }
        float minZoomRatio = camera.getCameraInfo().getZoomState().getValue().getMinZoomRatio();
        return new GetMinZoomRatioResult(minZoomRatio);
    }

    @Nullable
    public GetMaxZoomRatioResult getMaxZoomRatio() {
        if (camera == null) {
            return null;
        }
        float maxZoomRatio = camera.getCameraInfo().getZoomState().getValue().getMaxZoomRatio();
        return new GetMaxZoomRatioResult(maxZoomRatio);
    }

    public void disableTorch() {
        if (camera != null) {
            camera.getCameraControl().enableTorch(false);
        }
        isTorchEnabled = false;
    }

    public void handleGoogleBarcodeScannerModuleInstallProgress(
            @ModuleInstallStatusUpdate.InstallState int state,
            @Nullable Integer progress
    ) {
        plugin.notifyGoogleBarcodeScannerModuleInstallProgressListener(state, progress);
    }

    public boolean requestCameraPermissionIfNotDetermined(PluginCall call) throws Exception {
        PermissionState state = getCameraPermission();
        if (state == PermissionState.GRANTED) {
            return true;
        } else if (state == PermissionState.DENIED) {
            throw new Exception(BarcodeScannerPlugin.ERROR_PERMISSION_DENIED);
        } else {
            requestCameraPermission(call);
            return false;
        }
    }

    public PermissionState getCameraPermission() {
        return plugin.getPermissionState(BarcodeScannerPlugin.CAMERA);
    }

    public void requestCameraPermission(PluginCall call) {
        plugin.requestPermissionForAlias(
                BarcodeScannerPlugin.CAMERA,
                call,
                "cameraPermissionsCallback"
        );
    }

    public void setZoomRatio(SetZoomRatioOptions options) {
        float zoomRatio = options.getZoomRatio();
        if (camera == null) {
            return;
        }
        camera.getCameraControl().setZoomRatio(zoomRatio);
    }

}
