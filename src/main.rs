extern crate sdl2;
extern crate core;

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
    let args: Vec<String> = env::args().collect();
    if args.len() == 1 {
        eprintln!("Error: must pass rom");
        return;
    }

    let path = args[1].to_string();
    let mut chip = cpu::CPU::new();

    let font: Vec<u8> = fs::read("./font.ch8")
        .expect("Couldn't read the file");
    chip.load_rom(font, cpu::FONT_OFFSET);

    let rom: Vec<u8> = fs::read(path)
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
