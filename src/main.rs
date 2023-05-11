extern crate sdl2;

use std::{env, fs};
use std::time::Duration;
use sdl2::pixels::Color;
use sdl2::event::Event;
use sdl2::keyboard::Keycode;

use crate::cpu::STATE::{DrawScreen, Halt};

mod cpu;
mod bit_utils;
mod display;

fn main() {
    let mut rom = "/Users/ruhickey/Downloads/IBM_Logo.ch8";

    for argument in env::args() {
        if argument == "pong" {
            rom = "/Users/ruhickey/Downloads/Pong.ch8";
        }
    }

    let mut chip = cpu::CPU::new();

    let font: Vec<u8> = fs::read("./font.ch8")
        .expect("Couldn't read the file");
    chip.load_rom(font, cpu::FONT_OFFSET);

    let rom: Vec<u8> = fs::read(rom)
        .expect("Couldn't read the file");
    chip.load_rom(rom, cpu::ROM_OFFSET);

    let mut display = display::Display::new();
    'running: loop {
        display.canvas.set_draw_color(Color::RGB(0, 0, 0));
        display.canvas.clear();
        for event in display.event_pump.poll_iter() {
            match event {
                Event::Quit {..} |
                Event::KeyDown { keycode: Some(Keycode::Escape), .. } => {
                    break 'running
                },
                _ => {}
            }
        }

        let instruction = chip.execute(10);

        if instruction == DrawScreen {
            display.draw_screen(chip.screen);
        } else if instruction == Halt {
            break 'running
        }

        ::std::thread::sleep(Duration::new(0, 1_000_000_000u32 / 60));
    }
}
