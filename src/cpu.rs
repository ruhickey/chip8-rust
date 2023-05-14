#![allow(dead_code)]
#![allow(non_snake_case)]

pub const FONT_OFFSET: usize = 0x50;
pub const ROM_OFFSET: usize = 0x200;
pub const SCREEN_WIDTH: usize = 64;
pub const SCREEN_HEIGHT: usize = 32;

use crate::bit_utils::{byte_from_short, nibble_from_short, short_from_bytes};
use crate::cpu::STATE::{Halt, IncrementPc, NoIncrementPc, DrawScreen, NoDrawScreen};

extern crate rand;

use rand::Rng;

#[derive(Debug)]
#[derive(PartialEq)]
pub enum STATE {
    IncrementPc,
    NoIncrementPc,
    Halt,
    DrawScreen,
    NoDrawScreen
}

#[derive(Debug)]
struct Registers {
    i: usize,
    pc: usize,
    sp: usize,
    v: [u8; 16]
}

#[derive(Debug)]
struct Timers {
    delay: u8,
    sound: u8,
}

#[derive(derivative::Derivative)]
#[derivative(Debug)]
pub struct CPU {
    #[derivative(Debug="ignore")]
    memory: [u8; 4096],
    registers: Registers,
    #[derivative(Debug="ignore")]
    pub screen: [u8; SCREEN_WIDTH * SCREEN_HEIGHT],
    stack: [usize; 16],
    timers: Timers
}

impl CPU {
    pub fn new() -> Self {
        return CPU {
            memory: [0; 4096],
            registers: Registers {
                i: 0,
                pc: ROM_OFFSET,
                sp: 0,
                v: [0; 16],
            },
            timers: Timers {
                delay: 0,
                sound: 0
            },
            screen: [0; SCREEN_WIDTH * SCREEN_HEIGHT],
            stack: [0; 16]
        }
    }

    pub fn reset_registers(&mut self) {
        self.registers = Registers {
            i: 0,
            pc: ROM_OFFSET,
            sp: 0,
            v: [0; 16],
        };

        self.stack = [0; 16];

        self.timers = Timers {
            delay: 0,
            sound: 0
        };
    }

    pub fn load_rom(&mut self, buffer: Vec<u8>, offset: usize) {
        for (idx, byte) in buffer.into_iter().enumerate() {
            self.memory[idx + offset] = byte;
        }
    }

    fn get_next_opcode(&mut self) -> Result<u16, String> {
        return short_from_bytes(self.memory[self.registers.pc], self.memory[self.registers.pc + 1]);
    }

    fn unknown_opcode(&mut self, opcode: u16) -> Result<STATE, String> {
        return Err(format!("Unknown opcode: 0x{:04X}", opcode));
    }

    fn clear_screen(&mut self) -> Result<STATE, String> {
        for i in 0..self.screen.len() {
            self.screen[i] = 0;
        }
        return Ok(IncrementPc);
    }

    fn return_from_subroutine(&mut self) -> Result<STATE, String> {
        self.registers.sp -= 1;
        self.registers.pc = self.stack[self.registers.sp];
        self.stack[self.registers.sp] = 0;
        return Ok(IncrementPc);
    }

    fn zero_opcode(&mut self, opcode: u16) -> Result<STATE, String> {
        if opcode == 0x00E0 {
            return self.clear_screen();
        } else if opcode == 0x00EE {
            return self.return_from_subroutine();
        }

        return Err(format!("unknown zero opcode: 0x{:04X}", opcode))
    }

    fn jump_opcode(&mut self, opcode: u16) -> Result<STATE, String> {
        let location = opcode & 0xFFF;
        self.registers.pc = location as usize;
        return Ok(NoIncrementPc);
    }

    fn subroutine_opcode(&mut self, opcode: u16) -> Result<STATE, String> {
        let location = opcode & 0xFFF;
        self.stack[self.registers.sp] = self.registers.pc;
        self.registers.pc = location as usize;
        self.registers.sp += 1;
        return Ok(NoIncrementPc);
    }

    fn skip_opcode(&mut self, opcode: u16) -> Result<STATE, String> {
        let op = nibble_from_short(opcode, 0)?;
        let vx = nibble_from_short(opcode, 1)?;
        let byte = byte_from_short(opcode, 1)?;

        if op == 0x3 {
            if self.registers.v[vx as usize] == byte {
                self.registers.pc += 2;
            }
            return Ok(IncrementPc);
        } else if op == 0x4 {
            if self.registers.v[vx as usize] != byte {
                self.registers.pc += 2;
            }
            return Ok(IncrementPc);
        }

        return Err(format!("unknown skip opcode: 0x{:04X}", opcode))
    }

    fn skip_if_vx_vy(&mut self, opcode: u16) -> Result<STATE, String> {
        let vx = nibble_from_short(opcode, 1)?;
        let vy = nibble_from_short(opcode, 2)?;

        if self.registers.v[vx as usize] == self.registers.v[vy as usize] {
            self.registers.pc += 2;
        }

        return Ok(IncrementPc);
    }

    fn skip_ne_vx_vy(&mut self, opcode: u16) -> Result<STATE, String> {
        let vx = nibble_from_short(opcode, 1)?;
        let vy = nibble_from_short(opcode, 2)?;

        if self.registers.v[vx as usize] != self.registers.v[vy as usize] {
            self.registers.pc += 2;
        }

        return Ok(IncrementPc);
    }

    fn add_kk_to_vx(&mut self, opcode: u16) -> Result<STATE, String> {
        let vx = nibble_from_short(opcode, 1)?;
        let kk = byte_from_short(opcode, 1)?;
        self.registers.v[vx as usize] += kk;
        return Ok(IncrementPc);
    }

    fn set_vx_to_kk(&mut self, opcode: u16) -> Result<STATE, String> {
        let vx = nibble_from_short(opcode, 1)?;
        let op = byte_from_short(opcode, 1)?;
        self.registers.v[vx as usize] = op;
        return Ok(IncrementPc);
    }

    fn set_vx_to_vy(&mut self, opcode: u16) -> Result<STATE, String> {
        let vx = nibble_from_short(opcode, 1)?;
        let vy = nibble_from_short(opcode, 2)?;

        self.registers.v[vx as usize] = self.registers.v[vy as usize];
        return Ok(IncrementPc);
    }

    fn or_vx_vy(&mut self, opcode: u16) -> Result<STATE, String> {
        let vx = nibble_from_short(opcode, 1)?;
        let vy = nibble_from_short(opcode, 2)?;

        self.registers.v[vx as usize] |= self.registers.v[vy as usize];
        return Ok(IncrementPc);
    }

    fn and_vx_vy(&mut self, opcode: u16) -> Result<STATE, String> {
        let vx = nibble_from_short(opcode, 1)?;
        let vy = nibble_from_short(opcode, 2)?;

        self.registers.v[vx as usize] &= self.registers.v[vy as usize];
        return Ok(IncrementPc);
    }

    fn xor_vx_vy(&mut self, opcode: u16) -> Result<STATE, String> {
        let vx = nibble_from_short(opcode, 1)?;
        let vy = nibble_from_short(opcode, 2)?;

        self.registers.v[vx as usize] ^= self.registers.v[vy as usize];
        return Ok(IncrementPc);
    }

    fn add_vx_vy_carry(&mut self, opcode: u16) -> Result<STATE, String> {
        let vx = nibble_from_short(opcode, 1)?;
        let vy = nibble_from_short(opcode, 2)?;

        let x = self.registers.v[vx as usize];
        let y = self.registers.v[vy as usize];
        let sum = x.wrapping_add(y);

        self.registers.v[vx as usize] = sum;

        if sum < x && sum < y {
            self.registers.v[0xF] = 1;
        } else {
            self.registers.v[0xF] = 0;
        }

        return Ok(IncrementPc);
    }

    fn sub_vx_vy_overflow(&mut self, opcode: u16) -> Result<STATE, String> {
        let vx = nibble_from_short(opcode, 1)?;
        let vy = nibble_from_short(opcode, 2)?;

        let x = self.registers.v[vx as usize];
        let y = self.registers.v[vy as usize];

        self.registers.v[vx as usize] = x.wrapping_sub(y);

        if x > y {
            self.registers.v[0xF] = 1;
        } else {
            self.registers.v[0xF] = 0;
        }

        return Ok(IncrementPc);
    }

    fn sub_vy_yx_overflow(&mut self, opcode: u16) -> Result<STATE, String> {
        let vx = nibble_from_short(opcode, 1)?;
        let vy = nibble_from_short(opcode, 2)?;

        let x = self.registers.v[vx as usize];
        let y = self.registers.v[vy as usize];

        self.registers.v[vx as usize] = y.wrapping_sub(x);

        if y > x {
            self.registers.v[0xF] = 1;
        } else {
            self.registers.v[0xF] = 0;
        }

        return Ok(IncrementPc);
    }

    fn bit_shift_right(& mut self, opcode: u16) -> Result<STATE, String> {
        let vx = nibble_from_short(opcode, 1)?;

        self.registers.v[0xF] = self.registers.v[vx as usize] & 0x1;
        self.registers.v[vx as usize] = self.registers.v[vx as usize] >> 1;

        return Ok(IncrementPc);
    }

    fn bit_shift_left(& mut self, opcode: u16) -> Result<STATE, String> {
        let vx = nibble_from_short(opcode, 1)?;

        self.registers.v[0xF] = (self.registers.v[vx as usize] >> 7) & 0x1;
        self.registers.v[vx as usize] = self.registers.v[vx as usize] << 1;

        return Ok(IncrementPc);
    }

    fn bit_ops_vx_vy(&mut self, opcode: u16) -> Result<STATE, String> {
        let op = nibble_from_short(opcode, 3)?;

        let ret = match op {
            0x0 => self.set_vx_to_vy(opcode),
            0x1 => self.or_vx_vy(opcode),
            0x2 => self.and_vx_vy(opcode),
            0x3 => self.xor_vx_vy(opcode),
            0x4 => self.add_vx_vy_carry(opcode),
            0x5 => self.sub_vx_vy_overflow(opcode),
            0x6 => self.bit_shift_right(opcode),
            0x7 => self.sub_vy_yx_overflow(opcode),
            0xE => self.bit_shift_left(opcode),
            _ => return Err(format!("unknown bit ops code: 0x{:X}", op))
        };

        return ret;
    }

    fn set_index_register(&mut self, opcode: u16) -> Result<STATE, String> {
        self.registers.i = (opcode & 0xFFF) as usize;
        return Ok(IncrementPc);
    }

    fn draw_sprite(&mut self, opcode: u16) -> Result<STATE, String> {
        let vx = nibble_from_short(opcode, 1)?;
        let vy = nibble_from_short(opcode, 2)?;
        let n = nibble_from_short(opcode, 3)?;

        self.registers.v[0xF] = 0;

        for y_idx in 0..n {
            let mut pixels: [u8; 8] = [0; 8];
            let byte = self.memory[self.registers.i + (y_idx as usize)];

            for i in 0..8 {
                pixels[7 - i] = (byte >> i) & 1;
            }

            let y_pixel = (self.registers.v[vy as usize] + y_idx) % 32;

            for x_idx in 0..pixels.len() {
                let pixel = pixels[x_idx];
                let x_pixel = (self.registers.v[vx as usize] + x_idx as u8) % 64;
                // TODO: Maybe fix this -1 situation.
                let pixel_index = (((y_pixel as usize) * SCREEN_WIDTH) + (x_pixel as usize)) - 1;
                let old_pixel = self.screen[pixel_index];
                self.screen[pixel_index] ^= pixel;

                if old_pixel == pixel {
                    self.registers.v[0xF] = 1;
                }
            }
        }

        return Ok(DrawScreen);
    }

    fn store_bcd_repr(&mut self, opcode: u16) -> Result<STATE, String> {
        let vx = nibble_from_short(opcode, 1)? as usize;
        let mut num = self.registers.v[vx];
        for i in 0..3 {
            self.memory[self.registers.i + (2 - i)] = num % 10;
            num /= 10;
        }
        return Ok(IncrementPc);
    }

    fn store_vx_values(&mut self, opcode: u16) -> Result<STATE, String> {
        let n = nibble_from_short(opcode, 1)?;
        for i in 0..(n + 1) {
            self.memory[self.registers.i + i as usize] = self.registers.v[i as usize];
        }
        return Ok(IncrementPc);
    }

    fn read_vx_values(&mut self, opcode: u16) -> Result<STATE, String> {
        let n = nibble_from_short(opcode, 1)?;
        for i in 0..(n + 1) {
            self.registers.v[i as usize] = self.memory[self.registers.i + i as usize];
        }
        return Ok(IncrementPc);
    }

    fn set_vx_to_delay(&mut self, opcode: u16) -> Result<STATE, String> {
        let vx = nibble_from_short(opcode, 1)?;
        self.registers.v[vx as usize] = self.timers.delay;
        return Ok(IncrementPc);
    }

    fn set_delay_to_vx(&mut self, opcode: u16) -> Result<STATE, String> {
        let vx = nibble_from_short(opcode, 1)?;
        self.timers.delay = self.registers.v[vx as usize];
        return Ok(IncrementPc);
    }

    fn set_sound_to_vx(&mut self, opcode: u16) -> Result<STATE, String> {
        let vx = nibble_from_short(opcode, 1)?;
        self.timers.sound = self.registers.v[vx as usize];
        return Ok(IncrementPc);
    }

    fn load_routines(&mut self, opcode: u16) -> Result<STATE, String> {
        let op = byte_from_short(opcode, 1)?;

        return match op {
            0x07 => self.set_vx_to_delay(opcode),
            0x15 => self.set_delay_to_vx(opcode),
            0x18 => self.set_sound_to_vx(opcode),
            0x29 => self.set_sprite_loc(opcode),
            0x33 => self.store_bcd_repr(opcode),
            0x55 => self.read_vx_values(opcode),
            0x65 => self.store_vx_values(opcode),
            _ => self.unknown_opcode(opcode)
        }
    }

    fn set_sprite_loc(&mut self, opcode: u16) -> Result<STATE, String> {
        let vx = nibble_from_short(opcode, 1)?;
        let char = self.registers.v[vx as usize];
        self.registers.i = FONT_OFFSET + (5 * char as usize);
        return Ok(IncrementPc);
    }

    fn jump_nnn_v0(&mut self, opcode: u16) -> Result<STATE, String> {
        self.registers.pc = (opcode & 0xFFF) as usize;
        self.registers.pc += self.registers.v[0x0] as usize;
        return Ok(IncrementPc);
    }

    fn random_u8_masked(&mut self, opcode: u16) -> Result<STATE, String> {
        let vx = nibble_from_short(opcode, 1)?;
        let mask = byte_from_short(opcode, 1)?;
        let rand_num: u8 = rand::thread_rng().gen();
        self.registers.v[vx as usize] = rand_num & mask;
        return Ok(IncrementPc);
    }

    fn run_opcode(&mut self, opcode: u16) -> Result<STATE, String> {
        let op = match nibble_from_short(opcode, 0) {
            Ok(n) => n,
            Err(msg) => return Err(msg)
        };

        return match op {
            0x0 => self.zero_opcode(opcode),
            0x1 => self.jump_opcode(opcode),
            0x2 => self.subroutine_opcode(opcode),
            0x3 => self.skip_opcode(opcode),
            0x4 => self.skip_opcode(opcode),
            0x5 => self.skip_if_vx_vy(opcode),
            0x6 => self.set_vx_to_kk(opcode),
            0x7 => self.add_kk_to_vx(opcode),
            0x8 => self.bit_ops_vx_vy(opcode),
            0x9 => self.skip_ne_vx_vy(opcode),
            0xA => self.set_index_register(opcode),
            0xB => self.jump_nnn_v0(opcode),
            0xC => self.random_u8_masked(opcode),
            0xD => self.draw_sprite(opcode),
            0xE => self.unknown_opcode(opcode),
            0xF => self.load_routines(opcode),
            _ => self.unknown_opcode(opcode)
        }
    }

    pub fn decrement_delay_timer(&mut self) {
        if self.timers.delay > 0 {
            self.timers.delay -= 1;
        }
    }

    fn increment_pc(&mut self) {
        self.registers.pc += 2;
    }

    pub fn execute(&mut self, n: u32) -> STATE {
        for _ in 0..n {
            let opcode = self.get_next_opcode().expect("opcode error");
            println!("0x{:04X}", opcode);
            match self.run_opcode(opcode) {
                Ok(state) => {
                    match state {
                        IncrementPc => self.increment_pc(),
                        DrawScreen => {
                            self.increment_pc();
                            return DrawScreen;
                        }
                        _ => {}
                    }
                },
                Err(msg) => {
                    eprintln!("{}", msg);
                    return Halt;
                }
            }
        }
        return NoDrawScreen
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test] // 00E0
    fn test_clear_screen() {
        let mut cpu = CPU::new();
        cpu.screen = [1; 2048];
        cpu.run_opcode(0x00E0).expect("opcode error");
        assert_eq!(cpu.screen, [0; 2048]);
    }

    #[test] // 00EE
    fn test_return_subroutine() {
        let mut cpu = CPU::new();
        let pc = cpu.registers.pc;
        cpu.run_opcode(0x2157).expect("opcode error");
        cpu.run_opcode(0x00EE).expect("opcode error");
        assert_eq!(cpu.registers.pc, pc);
    }

    #[test] // 1nnn
    fn test_jump() {
        let mut cpu = CPU::new();
        cpu.run_opcode(0x1157).expect("opcode error");
        assert_eq!(cpu.registers.pc, 0x157);
    }

    #[test] // 2nnn
    fn test_enter_subroutine() {
        let mut cpu = CPU::new();
        let pc = cpu.registers.pc;
        cpu.run_opcode(0x2157).expect("opcode error");
        assert_eq!(cpu.registers.pc, 0x157);
        assert_eq!(cpu.stack[0], pc);
    }

    #[test] // 3xkk
    fn test_skip_vx_equal() {
        let mut cpu = CPU::new();
        let pc = cpu.registers.pc;
        cpu.registers.v[0xA] = 0xCC;

        cpu.run_opcode(0x3A00).expect("opcode error");
        assert_eq!(pc, cpu.registers.pc);

        cpu.run_opcode(0x3ACC).expect("opcode error");
        assert_eq!(pc + 2, cpu.registers.pc);
    }

    #[test] // 4xkk
    fn test_skip_vx_not_equal() {
        let mut cpu = CPU::new();
        let pc = cpu.registers.pc;
        cpu.registers.v[0xA] = 0xCC;

        cpu.run_opcode(0x4ACC).expect("opcode error");
        assert_eq!(pc, cpu.registers.pc);

        cpu.run_opcode(0x4A00).expect("opcode error");
        assert_eq!(pc + 2, cpu.registers.pc);
    }

    #[test] // 5xy0
    fn test_skip_vx_equal_vy() {
        let mut cpu = CPU::new();
        let mut current_pc = cpu.registers.pc;
        cpu.registers.v[0xA] = 0xCC;
        cpu.registers.v[0xB] = 0xCC;
        cpu.registers.v[0xC] = 0x00;

        cpu.run_opcode(0x5AB0).expect("opcode error");
        assert_eq!(cpu.registers.pc, current_pc + 2);

        current_pc = cpu.registers.pc;
        cpu.run_opcode(0x5AC0).expect("opcode error");
        assert_eq!(cpu.registers.pc, current_pc);
    }

    #[test] // 6xkk
    fn test_set_vx_to_kk() {
        let mut cpu = CPU::new();
        cpu.run_opcode(0x6ACC).expect("opcode error");
        assert_eq!(cpu.registers.v[0xA], 0xCC);
    }

    #[test] // 7xkk
    fn test_add_kk_to_vx() {
        let mut cpu = CPU::new();
        cpu.registers.v[0xA] = 0x20;
        cpu.run_opcode(0x7A02).expect("opcode error");
        assert_eq!(cpu.registers.v[0xA], 0x22);
    }

    #[test] // 8xy0
    fn test_set_vx_to_vy() {
        let mut cpu = CPU::new();
        cpu.registers.v[0xB] = 0x20;
        cpu.run_opcode(0x8AB0).expect("opcode error");
        assert_eq!(cpu.registers.v[0xA], 0x20);
    }

    #[test] // 8xy1
    fn test_or_vx_vy() {
        let mut cpu = CPU::new();
        cpu.registers.v[0xA] = 0x0;
        cpu.registers.v[0xB] = 0x1;
        cpu.run_opcode(0x8AB1).expect("opcode error");
        assert_eq!(cpu.registers.v[0xA], 0x1);
    }

    #[test] // 8xy2
    fn test_and_vx_vy() {
        let mut cpu = CPU::new();
        cpu.registers.v[0xA] = 0x3;
        cpu.registers.v[0xB] = 0x1;
        cpu.run_opcode(0x8AB2).expect("opcode error");
        assert_eq!(cpu.registers.v[0xA], 0x1);
    }

    #[test] // 8xy3
    fn test_xor_vx_vy() {
        let mut cpu = CPU::new();
        cpu.registers.v[0xA] = 0x1;
        cpu.registers.v[0xB] = 0x2;
        cpu.run_opcode(0x8AB3).expect("opcode error");
        assert_eq!(cpu.registers.v[0xA], 0x3);
    }

    #[test] // 8xy4
    fn test_sum_carry_flag() {
        let mut cpu = CPU::new();
        // Make sure the carry flag gets set
        cpu.registers.v[0xA] = 0x8F;
        cpu.registers.v[0xB] = 0x8F;
        cpu.run_opcode(0x8AB4).expect("opcode error");
        assert_eq!(cpu.registers.v[0xA], 0x1E);
        assert_eq!(cpu.registers.v[0xF], 0x1);

        // Make sure the carry flag doesn't get set
        cpu.reset_registers();
        cpu.registers.v[0xA] = 0x78;
        cpu.registers.v[0xB] = 0x78;
        cpu.run_opcode(0x8AB4).expect("opcode error");
        assert_eq!(cpu.registers.v[0xA], 0xF0);
        assert_eq!(cpu.registers.v[0xF], 0x0);
    }

    #[test] // 8xy5
    fn test_sub_vx_vy_not_borrow() {
        let mut cpu = CPU::new();
        cpu.registers.v[0xA] = 0x8F;
        cpu.registers.v[0xB] = 0x8A;
        cpu.run_opcode(0x8AB5).expect("opcode error");
        assert_eq!(cpu.registers.v[0xA], 0x5);
        assert_eq!(cpu.registers.v[0xF], 0x1);

        cpu.reset_registers();
        cpu.registers.v[0xA] = 0x8A;
        cpu.registers.v[0xB] = 0x8F;
        cpu.run_opcode(0x8AB5).expect("opcode error");
        assert_eq!(cpu.registers.v[0xA], 0xFB);
        assert_eq!(cpu.registers.v[0xF], 0x0);
    }

    #[test] // 8xy6
    fn test_bit_shift_right() {
        let mut cpu = CPU::new();
        cpu.registers.v[0xA] = 0b11010100;
        cpu.run_opcode(0x8A06).expect("opcode error");
        assert_eq!(cpu.registers.v[0xA], 0b01101010);
        assert_eq!(cpu.registers.v[0xF], 0x0);

        cpu.reset_registers();
        cpu.registers.v[0xA] = 0b11010101;
        cpu.run_opcode(0x8A06).expect("opcode error");
        assert_eq!(cpu.registers.v[0xA], 0b01101010);
        assert_eq!(cpu.registers.v[0xF], 0x1);
    }

    #[test] // 8xy7
    fn test_sub_vy_vx_not_borrow() {
        let mut cpu = CPU::new();
        cpu.registers.v[0xA] = 0x8F;
        cpu.registers.v[0xB] = 0x8A;
        cpu.run_opcode(0x8AB7).expect("opcode error");
        assert_eq!(cpu.registers.v[0xA], 0xFB);
        assert_eq!(cpu.registers.v[0xF], 0x0);

        cpu.reset_registers();
        cpu.registers.v[0xA] = 0x8A;
        cpu.registers.v[0xB] = 0x8F;
        cpu.run_opcode(0x8AB7).expect("opcode error");
        assert_eq!(cpu.registers.v[0xA], 0x5);
        assert_eq!(cpu.registers.v[0xF], 0x1);
    }

    #[test] // 8xyE
    fn test_bit_shift_left() {
        let mut cpu = CPU::new();
        cpu.registers.v[0xA] = 0b10101010;
        cpu.run_opcode(0x8A0E).expect("opcode error");
        assert_eq!(cpu.registers.v[0xA], 0b01010100);
        assert_eq!(cpu.registers.v[0xF], 0x1);

        cpu.reset_registers();
        cpu.registers.v[0xA] = 0b01010100;
        cpu.run_opcode(0x8A0E).expect("opcode error");
        assert_eq!(cpu.registers.v[0xA], 0b10101000);
        assert_eq!(cpu.registers.v[0xF], 0x0);
    }

    #[test] // 9xy0
    fn test_skip_vx_not_vy() {
        let mut cpu = CPU::new();
        let mut current_pc = cpu.registers.pc;
        cpu.registers.v[0xA] = 1;
        cpu.registers.v[0xB] = 2;
        cpu.run_opcode(0x9AB0).expect("opcode error");
        assert_eq!(cpu.registers.pc, current_pc + 2);

        current_pc = cpu.registers.pc;
        cpu.registers.v[0xA] = 2;
        cpu.registers.v[0xB] = 2;
        cpu.run_opcode(0x9AB0).expect("opcode error");
        assert_eq!(cpu.registers.pc, current_pc);
    }

    #[test] // Annn
    fn test_set_index_register() {
        let mut cpu = CPU::new();
        cpu.run_opcode(0xA123).expect("opcode error");
        assert_eq!(cpu.registers.i, 0x123);
    }

    #[test] // Bnnn
    fn test_jump_nnn_v0() {
        let mut cpu = CPU::new();
        cpu.registers.v[0x0] = 0x10;
        cpu.run_opcode(0xB120).expect("opcode error");
        assert_eq!(cpu.registers.pc, 0x130);
    }

    #[test] // Ex9E
    fn test_Ex9E() {

    }

    #[test] // ExA1
    fn test_ExA1() {

    }

    #[test] // Fx07
    fn test_vx_as_delay() {
        let mut cpu = CPU::new();
        cpu.timers.delay = 0xBE;
        cpu.run_opcode(0xFA07).expect("opcode error");
        assert_eq!(cpu.registers.v[0xA], 0xBE);
    }

    #[test] // Fx0A
    fn test_Fx0A() {

    }

    #[test] // Fx15
    fn test_delay_as_vx() {
        let mut cpu = CPU::new();
        cpu.registers.v[0xA] = 0xBE;
        cpu.run_opcode(0xFA15).expect("opcode error");
        assert_eq!(cpu.timers.delay, 0xBE);
    }

    #[test] // Fx18
    fn test_sound_as_vx() {
        let mut cpu = CPU::new();
        cpu.registers.v[0xA] = 0xBE;
        cpu.run_opcode(0xFA18).expect("opcode error");
        assert_eq!(cpu.timers.sound, 0xBE);
    }

    #[test] // Fx1E
    fn test_Fx1E() {

    }

    #[test] // Fx29
    fn test_set_sprite_loc() {
        let mut cpu = CPU::new();
        cpu.registers.v[0x1] = 0x0;
        cpu.run_opcode(0xF129).expect("opcode error");
        assert_eq!(cpu.registers.i, FONT_OFFSET);

        cpu.registers.v[0x1] = 0xA;
        cpu.run_opcode(0xF129).expect("opcode error");
        // Each character is 5 bytes, so we add 5 to every byte
        assert_eq!(cpu.registers.i, FONT_OFFSET + (0xA * 5));
    }

    #[test] // Fx33
    fn test_store_bcd_repr() {
        let mut cpu = CPU::new();
        cpu.registers.i = 200;
        cpu.registers.v[0xA] = 157;
        cpu.run_opcode(0xFA33).expect("opcode error");
        assert_eq!(cpu.memory[200], 1);
        assert_eq!(cpu.memory[201], 5);
        assert_eq!(cpu.memory[202], 7);
    }

    #[test] // Fx55
    fn test_read_registers() {
        let mut cpu = CPU::new();
        cpu.registers.i = 200;
        for i in 0..16 {
            cpu.memory[cpu.registers.i + i] = i as u8;
        }

        cpu.run_opcode(0xFF55).expect("opcode error");
        for i in 0..16 {
            assert_eq!(cpu.registers.v[i], i as u8);
        }
    }

    #[test] // Fx65
    fn test_store_registers() {
        let mut cpu = CPU::new();
        cpu.registers.i = 200;

        for i in 0..16 {
            cpu.registers.v[i] = i as u8;
        }

        cpu.run_opcode(0xFF65).expect("opcode error");
        for i in 0..16 {
            assert_eq!(cpu.memory[cpu.registers.i + i], i as u8);
        }
    }
}