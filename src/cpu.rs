#![allow(dead_code)]

pub const FONT_OFFSET: usize = 0x50;
pub const ROM_OFFSET: usize = 0x200;
pub const SCREEN_WIDTH: usize = 64;
pub const SCREEN_HEIGHT: usize = 32;

use crate::bit_utils::{byte_from_short, nibble_from_short, short_from_bytes};
use crate::cpu::STATE::{Halt, IncrementPc, NoIncrementPc, DrawScreen, NoDrawScreen};

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

    pub fn load_rom(&mut self, buffer: Vec<u8>, offset: usize) {
        for (idx, byte) in buffer.into_iter().enumerate() {
            self.memory[idx + offset] = byte;
        }
    }

    fn get_next_opcode(&mut self) -> Result<u16, String> {
        return short_from_bytes(self.memory[self.registers.pc], self.memory[self.registers.pc + 1]);
    }

    fn unknown_opcode(&mut self, opcode: u16) -> Result<STATE, String> {
        return Err(format!("Unknown opcode: 0x{:0>4X}", opcode));
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
        return Ok(NoIncrementPc);
    }

    fn zero_opcode(&mut self, opcode: u16) -> Result<STATE, String> {
        if opcode == 0x00E0 {
            return self.clear_screen();
        } else if opcode == 0x00EE {
            return self.return_from_subroutine();
        }

        return Err(format!("unknown zero opcode: 0x{:4>X}", opcode))
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
                return Ok(IncrementPc);
            }
            return Ok(NoIncrementPc);
        } else if op == 0x4 {
            if self.registers.v[vx as usize] != byte {
                return Ok(IncrementPc);
            }
            return Ok(NoIncrementPc);
        }

        return Err(format!("unknown skip opcode: 0x{:4>X}", opcode))
    }

    fn skip_if_vx_vy(&mut self, opcode: u16) -> Result<STATE, String> {
        let vx = nibble_from_short(opcode, 1)?;
        let vy = nibble_from_short(opcode, 2)?;

        if self.registers.v[vx as usize] == self.registers.v[vy as usize] {
            return Ok(IncrementPc);
        }

        return Ok(NoIncrementPc);
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

    fn bit_ops_vx_vy(&mut self, opcode: u16) -> Result<STATE, String> {
        let op = nibble_from_short(opcode, 3)?;

        let ret = match op {
            0x0 => self.set_vx_to_vy(opcode),
            0x1 => self.or_vx_vy(opcode),
            0x2 => self.and_vx_vy(opcode),
            0x3 => self.xor_vx_vy(opcode),
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

    fn load_routines(&mut self, opcode: u16) -> Result<STATE, String> {
        let op = byte_from_short(opcode, 1)?;
        return match op {
            0x33 => self.store_bcd_repr(opcode),
            _ => self.unknown_opcode(opcode)
        }
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
            0x9 => self.unknown_opcode(opcode),
            0xA => self.set_index_register(opcode),
            0xB => self.unknown_opcode(opcode),
            0xC => self.unknown_opcode(opcode),
            0xD => self.draw_sprite(opcode),
            0xE => self.unknown_opcode(opcode),
            0xF => self.load_routines(opcode),
            _ => self.unknown_opcode(opcode)
        }
    }

    fn increment_pc(&mut self) {
        self.registers.pc += 2;
    }

    pub fn execute(&mut self, n: u32) -> STATE {
        for _ in 0..n {
            let opcode = self.get_next_opcode().expect("opcode error");
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

    #[test]
    fn test_clear_screen() {
        let mut cpu = CPU::new();
        cpu.screen = [1; 2048];
        cpu.run_opcode(0x00E0).expect("opcode error");
        assert_eq!(cpu.screen, [0; 2048]);
    }

    #[test]
    fn test_jump() {
        let mut cpu = CPU::new();
        cpu.run_opcode(0x1157).expect("opcode error");
        assert_eq!(cpu.registers.pc, 0x157);
    }

    #[test]
    fn test_enter_subroutine() {
        let mut cpu = CPU::new();
        let pc = cpu.registers.pc;
        cpu.run_opcode(0x2157).expect("opcode error");
        assert_eq!(cpu.registers.pc, 0x157);
        assert_eq!(cpu.stack[0], pc);
    }

    #[test]
    fn test_return_subroutine() {
        let mut cpu = CPU::new();
        let pc = cpu.registers.pc;
        cpu.run_opcode(0x2157).expect("opcode error");
        cpu.run_opcode(0x00EE).expect("opcode error");
        assert_eq!(cpu.registers.pc, pc);
    }

    #[test]
    fn test_skip_vx_equal() {
        let mut cpu = CPU::new();
        cpu.registers.v[0xA] = 0xCC;

        let mut increment = cpu.run_opcode(0x3ACC).expect("opcode error");
        assert_eq!(increment, IncrementPc);

        increment = cpu.run_opcode(0x3ACD).expect("opcode error");
        assert_eq!(increment, NoIncrementPc);
    }

    #[test]
    fn test_skip_vx_not_equal() {
        let mut cpu = CPU::new();
        cpu.registers.v[0xA] = 0xCC;

        let mut increment = cpu.run_opcode(0x4ACC).expect("opcode error");
        assert_eq!(increment, NoIncrementPc);

        increment = cpu.run_opcode(0x4ACD).expect("opcode error");
        assert_eq!(increment, IncrementPc);
    }

    #[test]
    fn test_skip_vx_equal_vy() {
        let mut cpu = CPU::new();
        cpu.registers.v[0xA] = 0xCC;
        cpu.registers.v[0xB] = 0xCC;
        cpu.registers.v[0xC] = 0x00;

        let mut increment = cpu.run_opcode(0x5AB0).expect("opcode error");
        assert_eq!(increment, IncrementPc);

        increment = cpu.run_opcode(0x5AC0).expect("opcode error");
        assert_eq!(increment, NoIncrementPc);
    }

    #[test]
    fn test_set_vx_to_kk() {
        let mut cpu = CPU::new();
        cpu.run_opcode(0x6ACC).expect("opcode error");
        assert_eq!(cpu.registers.v[0xA], 0xCC);
    }

    #[test]
    fn test_add_kk_to_vx() {
        let mut cpu = CPU::new();
        cpu.registers.v[0xA] = 0x20;
        cpu.run_opcode(0x7A02).expect("opcode error");
        assert_eq!(cpu.registers.v[0xA], 0x22);
    }

    #[test]
    fn test_set_vx_to_vy() {
        let mut cpu = CPU::new();
        cpu.registers.v[0xB] = 0x20;
        cpu.run_opcode(0x8AB0).expect("opcode error");
        assert_eq!(cpu.registers.v[0xA], 0x20);
    }

    #[test]
    fn test_or_vx_vy() {
        let mut cpu = CPU::new();
        cpu.registers.v[0xA] = 0x0;
        cpu.registers.v[0xB] = 0x1;
        cpu.run_opcode(0x8AB1).expect("opcode error");
        assert_eq!(cpu.registers.v[0xA], 0x1);
    }

    #[test]
    fn test_and_vx_vy() {
        let mut cpu = CPU::new();
        cpu.registers.v[0xA] = 0x3;
        cpu.registers.v[0xB] = 0x1;
        cpu.run_opcode(0x8AB2).expect("opcode error");
        assert_eq!(cpu.registers.v[0xA], 0x1);
    }

    #[test]
    fn test_xor_vx_vy() {
        let mut cpu = CPU::new();
        cpu.registers.v[0xA] = 0x1;
        cpu.registers.v[0xB] = 0x2;
        cpu.run_opcode(0x8AB3).expect("opcode error");
        assert_eq!(cpu.registers.v[0xA], 0x3);
    }

    #[test]
    fn test_set_index_register() {
        let mut cpu = CPU::new();
        cpu.run_opcode(0xA123).expect("opcode error");
        assert_eq!(cpu.registers.i, 0x123);
    }

    #[test]
    fn test_store_bcd_repr() {
        let mut cpu = CPU::new();
        cpu.registers.i = 200;
        cpu.registers.v[0xA] = 157;
        cpu.run_opcode(0xFA33).expect("opcode error");
        assert_eq!(cpu.memory[200], 1);
        assert_eq!(cpu.memory[201], 5);
        assert_eq!(cpu.memory[202], 7);
    }
}