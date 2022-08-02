#![no_std]
#![no_main]

use hal::delay::Delay;
use hal::prelude::*;
use hal::{
    gpio::{Alternate, OpenDrain, H8},
    i2c::{Config, I2c},
    pac::I2C1,
};
use ms5837_example as _;
use stm32l4xx_hal as hal; // memory layout + panic handler

type I2C = hal::i2c::I2c<
    I2C1,
    (
        hal::gpio::Pin<Alternate<OpenDrain, 4>, H8, 'A', 9>,
        hal::gpio::Pin<Alternate<OpenDrain, 4>, H8, 'A', 10>,
    ),
>;

// See https://crates.io/crates/defmt-test/0.3.0 for more documentation (e.g. about the 'state'
// feature)
#[defmt_test::tests]
mod tests {
    use super::*;
    use defmt::assert;

    #[init]
    fn init() -> Option<(I2C, Delay)> {
        let dp = hal::pac::Peripherals::take().unwrap();
        let cp = hal::pac::CorePeripherals::take().unwrap();

        let mut flash = dp.FLASH.constrain();
        let mut rcc = dp.RCC.constrain();
        let mut pwr = dp.PWR.constrain(&mut rcc.apb1r1);

        let clocks = rcc.cfgr.freeze(&mut flash.acr, &mut pwr);

        let delay = Delay::new(cp.SYST, clocks);
        let mut gpioa = dp.GPIOA.split(&mut rcc.ahb2);

        let mut scl = gpioa.pa9.into_alternate_open_drain(
            &mut gpioa.moder,
            &mut gpioa.otyper,
            &mut gpioa.afrh,
        );
        scl.internal_pull_up(&mut gpioa.pupdr, true);

        let mut sda = gpioa.pa10.into_alternate_open_drain(
            &mut gpioa.moder,
            &mut gpioa.otyper,
            &mut gpioa.afrh,
        );
        sda.internal_pull_up(&mut gpioa.pupdr, true);

        Some((
            I2c::i2c1(
                dp.I2C1,
                (scl, sda),
                Config::new(100.kHz(), clocks),
                &mut rcc.apb1r1,
            ),
            delay,
        ))
    }

    #[test]
    fn device_init(handle: &mut Option<(I2C, Delay)>) {
        let (i2c, delay) = handle.take().unwrap();
        let ms5837 = ms5837::new(i2c, delay);
        let pressure_sensor = ms5837.init().unwrap();
        *handle = Some(pressure_sensor.release());
    }

    #[test]
    fn pressure_and_temperature(handle: &mut Option<(I2C, Delay)>) {
        let (i2c, delay) = handle.take().unwrap();
        let ms5837 = ms5837::new(i2c, delay);
        let mut pressure_sensor = ms5837.init().unwrap();
        let ms5837::TemperaturePressure {
            temperature,
            pressure,
        } = pressure_sensor
            .read_temperature_and_pressure(ms5837::OverSamplingRatio::R4096)
            .unwrap();
        defmt::println!(
            "Temperature: {:?} deg C, Pressure: {:?} mBar",
            temperature,
            pressure
        );
        // Assuming temperature is above 0deg C
        assert!(temperature > 0.0);
        // Max operating temperature.
        assert!(temperature < 85.0);
        // Assuming this test is not conducted below the water surface.
        assert!(pressure < 1050.0);
        // Assuming this test is not conducted above 5000m altitude.
        assert!(pressure > 400.0);

        *handle = Some(pressure_sensor.release());
    }

    #[test]
    fn over_sampling_ratio_conversion_time(handle: &mut Option<(I2C, Delay)>) {
        let (i2c, delay) = handle.take().unwrap();
        let ms5837 = ms5837::new(i2c, delay);
        let mut pressure_sensor = ms5837.init().unwrap();
        use ms5837::OverSamplingRatio::*;
        for r in [R256, R512, R1024, R2048, R4096].iter() {
            let _ = pressure_sensor.read_temperature_and_pressure(*r).unwrap();
        }
        *handle = Some(pressure_sensor.release());
    }
}
