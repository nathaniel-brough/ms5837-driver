#![no_std]
#![no_main]

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
    fn init() -> Option<I2C> {
        let dp = hal::pac::Peripherals::take().unwrap();

        let mut flash = dp.FLASH.constrain();
        let mut rcc = dp.RCC.constrain();
        let mut pwr = dp.PWR.constrain(&mut rcc.apb1r1);

        let clocks = rcc.cfgr.freeze(&mut flash.acr, &mut pwr);

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

        Some(I2c::i2c1(
            dp.I2C1,
            (scl, sda),
            Config::new(100.kHz(), clocks),
            &mut rcc.apb1r1,
        ))
    }

    #[test]
    fn device_init(i2c: &mut Option<I2C>) {
        let ms5837 = ms5837::new(i2c.take().unwrap());
        let pressure_sensor = ms5837.init().unwrap();
        *i2c = Some(pressure_sensor.release());
    }

    #[test]
    fn pressure_and_temperature(i2c: &mut Option<I2C>) {
        let ms5837 = ms5837::new(i2c.take().unwrap());
        let mut pressure_sensor = ms5837.init().unwrap();
        let temperature_and_pressure = pressure_sensor
            .read_temperature_and_pressure(ms5837::OverSamplingRatio::R4096)
            .unwrap();
        // This set of tests assume that you are;
        // 1. Above water
        // 2. Below 5km altitude
        // 3. Not freezing cold outside.
        assert!(temperature_and_pressure.temperature > 0.0);
        assert!(temperature_and_pressure.pressure > 1050.0);
        assert!(temperature_and_pressure.pressure < 400.0);
        *i2c = Some(pressure_sensor.release());
    }
}
