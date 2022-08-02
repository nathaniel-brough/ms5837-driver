#![no_main]
use embedded_hal_fuzz::{i2c::I2cFuzz, shared_data::FuzzData};
use libfuzzer_sys::fuzz_target;
use ms5837::OverSamplingRatio;

type Error = ();

fuzz_target!(|data: &[u8]| {
    let data = FuzzData::new(data);
    let i2c: I2cFuzz<'_, Error> = I2cFuzz::new(data);
    let pressure_sensor = ms5837::new(i2c, ms5837::mock_utils::SleepNop);
    if let Ok(mut pressure_sensor) = pressure_sensor.init() {
        // We ignore the result as it is likely garbage. We don't care about
        // the result/error just if it crashes or not.
        let _ = pressure_sensor.read_temperature_and_pressure(OverSamplingRatio::R4096);
    }
});
