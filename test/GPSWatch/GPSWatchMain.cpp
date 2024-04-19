#include <stdio.h>
#include <unistd.h>
#include "GPSWatch.h"

struct GPSWatchGpsData* input_gpsData() {
    printf("[GPS]  : 00:00:10\n");
    return GPSWatchGpsData_GpsData(GPSWatchTime_Time(TupleIntIntInt_Cons(0, 0, 10)));
}

int input_pulse1s() {
    sleep(1);
    return 1;
}

void output_time(struct GPSWatchTime* time) {
    printf("[DISP] : %02d:%02d:%02d\n", time->value.Time->member0, time->value.Time->member1, time->value.Time->member2);
}

void hook_gpsData_ModeGPSWatchGpsMode_On_to_ModeGPSWatchGpsMode_Sleep() {
    printf("[GPS]  : Go to sleep\n");
}

void hook_gpsData_ModeGPSWatchGpsMode_Sleep_to_ModeGPSWatchGpsMode_On() {
    printf("[GPS]  : Wake up\n");
}

int main() {
    activate();
    return 0;
}
