# XCios

XCios is a "power-mode-aware" FRP language for small embedded systems.

## Features

- Dynamic change of behavior, expressed in terms of state machine a la Statecharts
- Concise and safe description of power-mode management
  - Guarantees that I/O signals are not used in the wrong power mode
  - Enabling/disabling I/O devices is managed by the runtime

## Example: GPS Watch

```fsharp
# A GPS module has two power modes: Sleep and On.
mode GpsMode = Sleep | accessible On

switchmodule Main {
  in  pulse1s: Bool,
      # gpsData is an input signal of type GpsData from the GPS module that is accessible only in the On mode.
      gpsData: 'GpsMode GpsData
  out time(Time(23, 59, 55)): Time
  init Tick

  # Increment the time every second. We don't need data from the GPS module in this state so we set the mode of gpsData to Sleep.
  state Tick with gpsData >= Sleep {
    out node time =
      if pulse1s then add1s(time@last) else time@last

    # gpsData is in the Sleep mode, meaning gpsData is not accessible, so we can't use it here. If we try to use it, the compiler will give an error.
    # node invalid = getTime(gpsData)

    # Transition to the Adjust state at midnight.
    switch: if isZeroAM(time) then Adjust else Retain
  }

  # Adjust the time at midnight using the GPS data. So here we set the mode of gpsData to On.
  state Adjust with gpsData >= On {
    out node time = getTime(gpsData)

    # Go back to the Tick state after adjusting the time.
    switch: Tick
  }
}

type Time = Time of (Int, Int, Int)

type GpsData = GpsData of Time

fun add1s(time) = case time of
  Time(23, 59, 59) -> Time(0, 0, 0);
  Time(h, 59, 59) -> Time(h + 1, 0, 0);
  Time(h, m, 59) -> Time(h, m + 1, 0);
  Time(h, m, s) -> Time(h, m, s + 1);

fun isZeroAM(time) = case time of
  Time(h, m, s) -> h == 0 && m == 0 && s == 0;

fun getTime(gpsData) = case gpsData of
  GpsData(time) -> time;
```

The following command will generate a C++ code named `GPSWatch.cpp` and `GPSWatch.h`.

```sh
dune exec src/main.exe -- test/GPSWatch/GPGWatch.xfrp
```

A wrapper program for the generated code is already provided (`GPSWatchMain.cpp`).
Compiling the generated code together with the wrapper program will produce an executable.

```sh
cd test/GPSWatch
g++ GPSWatchMain.cpp GPSWatch.cpp
```

You will see the following output when you run the executable.
Notice that the GPS module wakes up at midnight and goes to sleep after adjusting the time.

```plaintext
[DISP] : 23:59:56
[DISP] : 23:59:57
[DISP] : 23:59:58
[DISP] : 23:59:59
[DISP] : 00:00:00
[GPS]  : Wake up
[GPS]  : 00:00:10
[DISP] : 00:00:10
[GPS]  : Go to sleep
[DISP] : 00:00:11
[DISP] : 00:00:12
...
```
