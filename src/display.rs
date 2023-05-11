#![allow(dead_code)]

extern crate sdl2;

use sdl2::render::Canvas;
use sdl2::video::Window;
use sdl2::pixels::Color;
use sdl2::EventPump;
use sdl2::rect::Rect;

const SCALE: u32 = 10;

fn print_type_of<T>(_: &T) {
    println!("{}", std::any::type_name::<T>())
}

pub struct Display {
    pub canvas: Canvas<Window>,
    pub event_pump: EventPump,
}

impl Display {
    pub fn new() -> Self {
        let sdl_context = sdl2::init().unwrap();
        let video_subsystem = sdl_context.video().unwrap();

        let window = video_subsystem.window("Chip-8", 64 * SCALE, 32 * SCALE)
            .position_centered()
            .build()
            .unwrap();

        let mut canvas = window.into_canvas().build().unwrap();
        let event_pump = sdl_context.event_pump().unwrap();

        canvas.set_draw_color(Color::RGB(0, 0, 0));
        canvas.clear();
        canvas.present();

        return Display{
            canvas,
            event_pump
        }
    }

    pub fn draw_screen(&mut self, pixels: [u8; 2048]) {
        self.canvas.set_draw_color(Color::RGB(0, 0, 0));
        self.canvas.clear();

        for y_idx in 0..32 {
            for x_idx in 0..64 {
                let pixel_index = (y_idx * 64 + x_idx) as usize;
                let x_start = x_idx * SCALE;
                let y_start = y_idx * SCALE;

                if pixels[pixel_index] == 1 {
                    self.canvas.set_draw_color(Color::RGB(255, 255, 255));
                    self.canvas.fill_rect(Rect::new(
                        x_start.try_into().unwrap(),
                        y_start.try_into().unwrap(),
                        SCALE, SCALE)
                    ).expect("couldn't write pixel");
                }
            }
        }

        self.canvas.present();
    }
}