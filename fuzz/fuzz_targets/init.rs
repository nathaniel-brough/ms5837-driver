#![no_main]
use embedded_hal_fuzz::{i2c::I2cFuzz, shared_data::FuzzData};
use libfuzzer_sys::fuzz_target;

type Error = ();

fuzz_target!(|data: &[u8]| {
    let data = FuzzData::new(data);
    let i2c: I2cFuzz<'_, Error> = I2cFuzz::new(data);
    let pressure_sensor = ms5837::new(i2c, ms5837::mock_utils::SleepNop);
    // We ignore the result/error as we only care about potential crashes.
    let _ = pressure_sensor.init();
});
