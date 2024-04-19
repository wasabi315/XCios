#include <stdio.h>
#include <unistd.h>
#include "GPSWatch.h"

struct GPSWatchGpsData* input_gpsData() {
    printf("input_gpsData\n");
    return GPSWatchGpsData_GpsData(GPSWatchTime_Time(TupleIntIntInt_Cons(0, 0, 10)));
}

int input_tick() {
    sleep(1);
    printf("input_tick\n");
    return 1;
}

void output_time(struct GPSWatchTime* time) {
    printf("output_time\n");
    printf("Time: %d:%d:%d\n", time->value.Time->member0, time->value.Time->member1, time->value.Time->member2);
}

void hook_gpsData_ModeGPSWatchGpsMode_On_to_ModeGPSWatchGpsMode_Sleep() {
    printf("hook_gpsData_On_to_Sleep\n");
}

void hook_gpsData_ModeGPSWatchGpsMode_Sleep_to_ModeGPSWatchGpsMode_On() {
    printf("hook_gpsData_Sleep_to_On\n");
}

int main() {
    activate();
    return 0;
}
