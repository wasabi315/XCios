#include <stdio.h>
#include <unistd.h>
#include "GPSWatch2.h"

struct GPSWatch2GpsData* input_gpsData() {
    printf("[GPS]   : Fetching...\n");
    usleep(500000); // 0.5s
    printf("[GPS]   : 00:00:10, 35.6764, 139.6500\n");
    struct GPSWatch2Time* time = GPSWatch2Time_Time(TupleIntIntInt_Cons(0, 0, 38));
    struct GPSWatch2LocInfo* locInfo = GPSWatch2LocInfo_LocInfo(TupleDoubleDouble_Cons(35.6764, 139.6500));
    return GPSWatch2GpsData_GpsData(TupleGPSWatch2TimeGPSWatch2LocInfo_Cons(time, locInfo));
}

int input_showLoc() {
    static int count = 0;
    int res = count > 9;
    count = (count + 1) % 20;
    return res;
}

int input_adjust() {
    static int count = 0;
    int res = count == 24;
    count = (count + 1) % 25;
    return res;
}

int input_pulse1s() {
    sleep(1);
    return 1;
}

void output_locInfo(struct GPSWatch2LocInfo* locInfo) {
    printf("[LOC]   : %.04f, %.04f\n", locInfo->value.LocInfo->member0, locInfo->value.LocInfo->member1);
}

void output_time(struct GPSWatch2Time* time) {
    printf("[CLOCK] : %02d:%02d:%02d\n", time->value.Time->member0, time->value.Time->member1, time->value.Time->member2);
}

void hook_locInfo_ModeGPSWatch2LocDispMode_On_to_ModeGPSWatch2LocDispMode_Off2() {
    printf("[LOC]   : Turning off...\n");
    usleep(500000); // 0.5s
}

void hook_locInfo_ModeGPSWatch2LocDispMode_Off2_to_ModeGPSWatch2LocDispMode_On() {
    printf("[LOC]   : Turning on...\n");
    usleep(500000); // 0.5s
}

void hook_gpsData_ModeGPSWatch2GpsMode_HighAcc_to_ModeGPSWatch2GpsMode_LowAcc() {
    printf("[GPS]   : Changing to the low accuracy mode...\n");
    usleep(500000); // 0.5s
}

void hook_gpsData_ModeGPSWatch2GpsMode_HighAcc_to_ModeGPSWatch2GpsMode_Off() {
    printf("[GPS]   : Turning off...\n");
    usleep(500000); // 0.5s
}

void hook_gpsData_ModeGPSWatch2GpsMode_LowAcc_to_ModeGPSWatch2GpsMode_HighAcc() {
    printf("[GPS]   : Changing to the high accuracy mode...\n");
    usleep(500000); // 0.5s
}

void hook_gpsData_ModeGPSWatch2GpsMode_LowAcc_to_ModeGPSWatch2GpsMode_Off() {
    printf("[GPS]   : Turning off...\n");
    usleep(500000); // 0.5s
}

void hook_gpsData_ModeGPSWatch2GpsMode_Off_to_ModeGPSWatch2GpsMode_HighAcc() {
    printf("[GPS]   : Turning on...\n");
    usleep(500000); // 0.5s
}

void hook_gpsData_ModeGPSWatch2GpsMode_Off_to_ModeGPSWatch2GpsMode_LowAcc() {
    printf("[GPS]   : Turning on (low accuracy)...\n");
    usleep(500000); // 0.5s
}

int main() {
    activate();
    return 0;
}
