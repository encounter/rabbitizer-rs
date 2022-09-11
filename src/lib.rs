use std::{ffi::CStr, mem::MaybeUninit, ptr::null, str};

mod bindings {
    #![allow(unknown_lints)]
    #![allow(non_camel_case_types)]
    #![allow(non_snake_case)]
    #![allow(dead_code)]

    use std::cmp::Ordering;

    include!(concat!(env!("OUT_DIR"), "/bindings.rs"));

    pub type OperandCallback = unsafe extern "C" fn(
        self_: *const RabbitizerInstruction,
        dst: *mut cty::c_char,
        immOverride: *const cty::c_char,
        immOverrideLength: size_t,
    ) -> size_t;
    extern "C" {
        pub static mut instrOpercandCallbacks: [OperandCallback; 0usize];
    }

    impl PartialOrd for RabbitizerOperandType {
        fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
            (*self as u32).partial_cmp(&(*other as u32))
        }
    }

    impl PartialOrd for RabbitizerInstrId {
        fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
            (*self as u32).partial_cmp(&(*other as u32))
        }
    }
}

fn to_c_str(str: Option<&str>) -> (*const cty::c_char, bindings::size_t) {
    if let Some(str) = str {
        (str.as_ptr() as *const cty::c_char, str.len() as bindings::size_t)
    } else {
        (null(), 0)
    }
}

unsafe fn from_static_c_str(str: *const cty::c_char) -> Option<&'static str> {
    if str.is_null() {
        None
    } else {
        Some(str::from_utf8_unchecked(CStr::from_ptr(str).to_bytes()))
    }
}

pub type OperandType = bindings::RabbitizerOperandType;

impl bindings::RabbitizerOperandType {
    pub fn is_valid(self) -> bool {
        self > bindings::RabbitizerOperandType::RABBITIZER_OPERAND_TYPE_INVALID
            && self < bindings::RabbitizerOperandType::RABBITIZER_OPERAND_TYPE_MAX
    }
}

pub type InstrId = bindings::RabbitizerInstrId;

impl bindings::RabbitizerInstrId {
    pub fn get_opcode_name(self) -> Option<&'static str> {
        match self {
            InstrId::RABBITIZER_INSTR_ID_cpu_INVALID
            | InstrId::RABBITIZER_INSTR_ID_cpu_MAX
            | InstrId::RABBITIZER_INSTR_ID_rsp_MAX
            | InstrId::RABBITIZER_INSTR_ID_r5900_MAX => None,
            v if v < InstrId::RABBITIZER_INSTR_ID_ALL_MAX => unsafe {
                from_static_c_str(bindings::RabbitizerInstrId_getOpcodeName(self))
            },
            _ => None,
        }
    }
}

#[derive(Debug, Copy, Clone, Default, Eq, PartialEq)]
pub enum SimpleOperandType {
    #[default]
    Other,
    Imm,
    ImmBase, // <imm>(<base>)
    Label,
}

#[derive(Debug, Clone, Default, Eq, PartialEq)]
pub struct SimpleOperand {
    pub kind: SimpleOperandType,
    pub disassembled: String,
}

pub struct Instruction {
    instruction: bindings::RabbitizerInstruction,
    simple_operands: Option<[SimpleOperand; 4]>,
    simple_operand_count: usize,
}

impl Instruction {
    pub fn new(word: u32, vram: u32) -> Self {
        Self {
            instruction: unsafe {
                let mut inst: MaybeUninit<bindings::RabbitizerInstruction> = MaybeUninit::uninit();
                bindings::RabbitizerInstruction_init(inst.as_mut_ptr(), word, vram);
                bindings::RabbitizerInstruction_processUniqueId(inst.as_mut_ptr());
                inst.assume_init()
            },
            simple_operands: None,
            simple_operand_count: 0,
        }
    }

    pub fn new_rsp(word: u32, vram: u32) -> Self {
        Self {
            instruction: unsafe {
                let mut inst: MaybeUninit<bindings::RabbitizerInstruction> = MaybeUninit::uninit();
                bindings::RabbitizerInstructionRsp_init(inst.as_mut_ptr(), word, vram);
                bindings::RabbitizerInstructionRsp_processUniqueId(inst.as_mut_ptr());
                inst.assume_init()
            },
            simple_operands: None,
            simple_operand_count: 0,
        }
    }

    pub fn new_r5900(word: u32, vram: u32) -> Self {
        Self {
            instruction: unsafe {
                let mut inst: MaybeUninit<bindings::RabbitizerInstruction> = MaybeUninit::uninit();
                bindings::RabbitizerInstructionR5900_init(inst.as_mut_ptr(), word, vram);
                bindings::RabbitizerInstructionR5900_processUniqueId(inst.as_mut_ptr());
                inst.assume_init()
            },
            simple_operands: None,
            simple_operand_count: 0,
        }
    }

    pub fn raw(&self) -> u32 {
        unsafe { bindings::RabbitizerInstruction_getRaw(&self.instruction) }
    }

    pub fn immediate(&self) -> u32 {
        unsafe { bindings::RabbitizerInstruction_getImmediate(&self.instruction) }
    }

    pub fn processed_immediate(&self) -> i32 {
        unsafe { bindings::RabbitizerInstruction_getProcessedImmediate(&self.instruction) }
    }

    pub fn instr_index(&self) -> u32 {
        unsafe { bindings::RabbitizerInstruction_getInstrIndex(&self.instruction) }
    }

    pub fn instr_index_as_vram(&self) -> u32 {
        unsafe { bindings::RabbitizerInstruction_getInstrIndexAsVram(&self.instruction) }
    }

    pub fn branch_offset(&self) -> i32 {
        unsafe { bindings::RabbitizerInstruction_getBranchOffset(&self.instruction) }
    }

    pub fn generic_branch_offset(&self, current_vram: u32) -> i32 {
        unsafe {
            bindings::RabbitizerInstruction_getGenericBranchOffset(&self.instruction, current_vram)
        }
    }

    pub fn blank_out(&mut self) -> &mut Self {
        unsafe { bindings::RabbitizerInstruction_blankOut(&mut self.instruction) }
        self
    }

    pub fn is_implemented(&self) -> bool {
        unsafe { bindings::RabbitizerInstruction_isImplemented(&self.instruction) }
    }

    pub fn is_likely_handwritten(&self) -> bool {
        unsafe { bindings::RabbitizerInstruction_isLikelyHandwritten(&self.instruction) }
    }

    pub fn is_nop(&self) -> bool {
        unsafe { bindings::RabbitizerInstruction_isNop(&self.instruction) }
    }

    pub fn is_unconditional_branch(&self) -> bool {
        unsafe { bindings::RabbitizerInstruction_isUnconditionalBranch(&self.instruction) }
    }

    pub fn is_jr_ra(&self) -> bool {
        unsafe { bindings::RabbitizerInstruction_isJrRa(&self.instruction) }
    }

    pub fn is_jr_not_ra(&self) -> bool {
        unsafe { bindings::RabbitizerInstruction_isJrNotRa(&self.instruction) }
    }

    pub fn has_delay_slot(&self) -> bool {
        unsafe { bindings::RabbitizerInstruction_hasDelaySlot(&self.instruction) }
    }

    pub fn map_instr_to_type(&self) -> Option<&str> {
        unsafe {
            let ptr = bindings::RabbitizerInstruction_mapInstrToType(&self.instruction);
            if ptr.is_null() {
                return None;
            }
            CStr::from_ptr(ptr)
        }
        .to_str()
        .ok()
    }

    pub fn same_opcode(&self, other: &Instruction) -> bool {
        unsafe { bindings::RabbitizerInstruction_sameOpcode(&self.instruction, &other.instruction) }
    }

    pub fn same_opcode_but_different_arguments(&self, other: &Instruction) -> bool {
        unsafe {
            bindings::RabbitizerInstruction_sameOpcodeButDifferentArguments(
                &self.instruction,
                &other.instruction,
            )
        }
    }

    pub fn has_operand(&self, operand: OperandType) -> bool {
        unsafe { bindings::RabbitizerInstruction_hasOperand(&self.instruction, operand) }
    }

    pub fn has_operand_alias(&self, operand: OperandType) -> bool {
        unsafe { bindings::RabbitizerInstruction_hasOperandAlias(&self.instruction, operand) }
    }

    pub fn valid_bits(&self) -> u32 {
        unsafe { bindings::RabbitizerInstruction_getValidBits(&self.instruction) }
    }

    pub fn is_valid(&self) -> bool {
        unsafe { bindings::RabbitizerInstruction_isValid(&self.instruction) }
    }

    pub fn must_disasm_as_data(&self) -> bool {
        unsafe { bindings::RabbitizerInstruction_mustDisasmAsData(&self.instruction) }
    }

    pub fn disassemble_operands(&self, imm_override: Option<&str>) -> String {
        let (imm_override_ptr, imm_override_len) = to_c_str(imm_override);
        unsafe {
            let size = bindings::RabbitizerInstruction_getSizeForBufferOperandsDisasm(
                &self.instruction,
                imm_override_len,
            ) as usize;
            let mut dst = vec![0u8; size];
            let size = bindings::RabbitizerInstruction_disassembleOperands(
                &self.instruction,
                dst.as_mut_ptr() as *mut cty::c_char,
                imm_override_ptr,
                imm_override_len,
            ) as usize;
            dst.truncate(size);
            String::from_utf8_unchecked(dst)
        }
    }

    pub fn disassemble_instruction(&self, imm_override: Option<&str>, extra_ljust: u32) -> String {
        let (imm_override_ptr, imm_override_len) = to_c_str(imm_override);
        unsafe {
            let size = bindings::RabbitizerInstruction_getSizeForBufferInstrDisasm(
                &self.instruction,
                imm_override_len,
                extra_ljust as cty::c_int,
            ) as usize;
            let mut dst = vec![0u8; size];
            let size = bindings::RabbitizerInstruction_disassembleInstruction(
                &self.instruction,
                dst.as_mut_ptr() as *mut cty::c_char,
                imm_override_ptr,
                imm_override_len,
                extra_ljust as cty::c_int,
            ) as usize;
            dst.truncate(size);
            String::from_utf8_unchecked(dst)
        }
    }

    pub fn disassemble_as_data(&self, extra_ljust: u32) -> String {
        unsafe {
            let size = bindings::RabbitizerInstruction_getSizeForBufferDataDisasm(
                &self.instruction,
                extra_ljust as cty::c_int,
            ) as usize;
            let mut dst = vec![0u8; size];
            let size = bindings::RabbitizerInstruction_disassembleAsData(
                &self.instruction,
                dst.as_mut_ptr() as *mut cty::c_char,
                extra_ljust as cty::c_int,
            ) as usize;
            dst.truncate(size);
            String::from_utf8_unchecked(dst)
        }
    }

    pub fn disassemble(&self, imm_override: Option<&str>, extra_ljust: u32) -> String {
        let (imm_override_ptr, imm_override_len) = to_c_str(imm_override);
        unsafe {
            let size = bindings::RabbitizerInstruction_getSizeForBuffer(
                &self.instruction,
                imm_override_len,
                extra_ljust as cty::c_int,
            ) as usize;
            let mut dst = vec![0u8; size];
            let size = bindings::RabbitizerInstruction_disassemble(
                &self.instruction,
                dst.as_mut_ptr() as *mut cty::c_char,
                imm_override_ptr,
                imm_override_len,
                extra_ljust as cty::c_int,
            ) as usize;
            dst.truncate(size);
            String::from_utf8_unchecked(dst)
        }
    }

    pub fn disassemble_operand(&self, idx: usize) -> String {
        if (0..4).contains(&idx) {
            unsafe {
                let operand = (*self.instruction.descriptor).operands[idx];
                if operand.is_valid() {
                    let mut dst = vec![0u8; 25];
                    let cb = bindings::instrOpercandCallbacks.get_unchecked(operand as usize);
                    let size =
                        cb(&self.instruction, dst.as_mut_ptr() as *mut cty::c_char, null(), 0)
                            as usize;
                    dst.truncate(size);
                    return String::from_utf8_unchecked(dst);
                }
            }
        }
        String::new()
    }

    pub fn instr_id(&self) -> InstrId { self.instruction.uniqueId }

    pub fn instr_suffix(&self) -> String {
        unsafe {
            let size = bindings::RabbitizerInstrSuffix_getSizeForBuffer(
                &self.instruction,
                (*self.instruction.descriptor).instrSuffix,
            ) as usize;
            let mut dst = vec![0u8; size];
            let size = bindings::RabbitizerInstrSuffix_processSuffix(
                &self.instruction,
                dst.as_mut_ptr() as *mut cty::c_char,
                (*self.instruction.descriptor).instrSuffix,
            ) as usize;
            dst.truncate(size);
            String::from_utf8_unchecked(dst)
        }
    }

    pub fn simple_operands(&mut self) -> &[SimpleOperand] {
        if self.simple_operands.is_none() {
            let mut operands: [SimpleOperand; 4] = Default::default();
            for idx in 0..4 {
                unsafe {
                    let operand = (*self.instruction.descriptor).operands[idx];
                    if !operand.is_valid() {
                        self.simple_operand_count = idx;
                        break;
                    }
                    let kind = match operand {
                        bindings::RabbitizerOperandType::RABBITIZER_OPERAND_TYPE_IMM => {
                            SimpleOperandType::Imm
                        }
                        bindings::RabbitizerOperandType::RABBITIZER_OPERAND_TYPE_LABEL => {
                            SimpleOperandType::Label
                        }
                        bindings::RabbitizerOperandType::RABBITIZER_OPERAND_TYPE_IMM_base
                        | bindings::RabbitizerOperandType::RABBITIZER_OPERAND_TYPE_RSP_IMM_base => {
                            SimpleOperandType::ImmBase
                        }
                        _ => SimpleOperandType::Other,
                    };
                    if kind == SimpleOperandType::ImmBase {
                        operands[idx] = SimpleOperand {
                            kind,
                            disassembled: {
                                let mut dst = vec![0u8; 25];
                                let cb = bindings::instrOpercandCallbacks.get_unchecked(
                                    bindings::RabbitizerOperandType::RABBITIZER_OPERAND_TYPE_IMM
                                        as usize,
                                );
                                let size = cb(
                                    &self.instruction,
                                    dst.as_mut_ptr() as *mut cty::c_char,
                                    null(),
                                    0,
                                ) as usize;
                                dst.truncate(size);
                                String::from_utf8_unchecked(dst)
                            },
                        };
                        operands[idx + 1] = SimpleOperand {
                            kind: SimpleOperandType::Other,
                            disassembled: {
                                let mut dst = vec![0u8; 25];
                                let cb = bindings::instrOpercandCallbacks.get_unchecked(
                                    bindings::RabbitizerOperandType::RABBITIZER_OPERAND_TYPE_rs
                                        as usize,
                                );
                                let size = cb(
                                    &self.instruction,
                                    dst.as_mut_ptr() as *mut cty::c_char,
                                    null(),
                                    0,
                                ) as usize;
                                dst.truncate(size);
                                String::from_utf8_unchecked(dst)
                            },
                        };
                        self.simple_operand_count = idx + 2;
                        break;
                    } else {
                        operands[idx] =
                            SimpleOperand { kind, disassembled: self.disassemble_operand(idx) };
                    }
                }
            }
            self.simple_operands = Some(operands);
        }
        &self.simple_operands.as_ref().unwrap()[0..self.simple_operand_count]
    }

    pub fn is_branch(&self) -> bool { unsafe { (*self.instruction.descriptor).isBranch } }

    pub fn is_branch_likely(&self) -> bool {
        unsafe { (*self.instruction.descriptor).isBranchLikely }
    }

    pub fn is_jump(&self) -> bool { unsafe { (*self.instruction.descriptor).isJump } }

    pub fn is_trap(&self) -> bool { unsafe { (*self.instruction.descriptor).isTrap } }

    pub fn is_float(&self) -> bool { unsafe { (*self.instruction.descriptor).isFloat } }

    pub fn is_double(&self) -> bool { unsafe { (*self.instruction.descriptor).isDouble } }

    pub fn is_unsigned(&self) -> bool { unsafe { (*self.instruction.descriptor).isUnsigned } }

    pub fn modifies_rt(&self) -> bool { unsafe { (*self.instruction.descriptor).modifiesRt } }

    pub fn modifies_rd(&self) -> bool { unsafe { (*self.instruction.descriptor).modifiesRd } }

    pub fn not_emitted_by_compilers(&self) -> bool {
        unsafe { (*self.instruction.descriptor).notEmitedByCompilers }
    }

    pub fn can_be_hi(&self) -> bool { unsafe { (*self.instruction.descriptor).canBeHi } }

    pub fn can_be_lo(&self) -> bool { unsafe { (*self.instruction.descriptor).canBeLo } }

    pub fn does_link(&self) -> bool { unsafe { (*self.instruction.descriptor).doesLink } }

    pub fn does_dereference(&self) -> bool {
        unsafe { (*self.instruction.descriptor).doesDereference }
    }

    pub fn does_load(&self) -> bool { unsafe { (*self.instruction.descriptor).doesLoad } }

    pub fn does_store(&self) -> bool { unsafe { (*self.instruction.descriptor).doesStore } }

    pub fn maybe_is_move(&self) -> bool { unsafe { (*self.instruction.descriptor).maybeIsMove } }

    pub fn is_pseudo(&self) -> bool { unsafe { (*self.instruction.descriptor).isPseudo } }
}

impl Drop for Instruction {
    fn drop(&mut self) {
        unsafe {
            match self.instruction.category {
                bindings::RabbitizerInstrCategory::RABBITIZER_INSTRCAT_RSP => {
                    bindings::RabbitizerInstructionRsp_destroy(&mut self.instruction)
                }
                bindings::RabbitizerInstrCategory::RABBITIZER_INSTRCAT_R5900 => {
                    bindings::RabbitizerInstructionR5900_destroy(&mut self.instruction)
                }
                _ => bindings::RabbitizerInstruction_destroy(&mut self.instruction),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_disassemble() {
        assert_eq!(
            Instruction::new(0x8D4A7E18, 0x80000000).disassemble(None, 0),
            "lw          $t2, 0x7E18($t2)".to_string()
        );
        assert_eq!(
            Instruction::new(0x00004010, 0x80000000).disassemble(None, 0),
            "mfhi        $t0".to_string()
        );
        assert_eq!(
            Instruction::new(0x27BDFFE0, 0x80000000).disassemble(None, 0),
            "addiu       $sp, $sp, -0x20".to_string()
        );
    }

    #[test]
    fn test_disassemble_operand() {
        assert_eq!(
            Instruction::new(0x8D4A7E18, 0x80000000).disassemble_operand(0),
            "$t2".to_string()
        );
        assert_eq!(
            Instruction::new(0x8D4A7E18, 0x80000000).disassemble_operand(1),
            "0x7E18($t2)".to_string()
        );
        assert_eq!(Instruction::new(0x8D4A7E18, 0x80000000).disassemble_operand(2), "".to_string());
    }

    #[test]
    fn test_get_opcode_name() {
        assert_eq!(
            Instruction::new(0x8D4A7E18, 0x80000000).instr_id().get_opcode_name(),
            Some("lw")
        );
        assert_eq!(
            Instruction::new(0x00004010, 0x80000000).instr_id().get_opcode_name(),
            Some("mfhi")
        );
        assert_eq!(
            Instruction::new(0x27BDFFE0, 0x80000000).instr_id().get_opcode_name(),
            Some("addiu")
        );
        assert_eq!(
            Instruction::new(0x0080882d, 0x80000000).instr_id().get_opcode_name(),
            Some("daddu")
        );
        assert_eq!(
            Instruction::new(0xd42a0000, 0x80000000).instr_id().get_opcode_name(),
            Some("ldc1")
        );
        assert_eq!(Instruction::new(0x00000001, 0x80000000).instr_id().get_opcode_name(), None);
    }

    #[test]
    fn test_instr_suffix() {
        assert_eq!(Instruction::new(0x8D4A7E18, 0x80000000).instr_suffix(), "".to_string());
        // TODO test R5900_xyzw
    }

    #[test]
    fn test_simple_operands() {
        let mut instruction = Instruction::new(0x8D4A7E18, 0x80000000);
        let operands = instruction.simple_operands();
        assert_eq!(operands.len(), 3);
        assert_eq!(operands[0], SimpleOperand {
            kind: SimpleOperandType::Other,
            disassembled: "$t2".to_string()
        });
        assert_eq!(operands[1], SimpleOperand {
            kind: SimpleOperandType::ImmBase,
            disassembled: "0x7E18".to_string()
        });
        assert_eq!(operands[2], SimpleOperand {
            kind: SimpleOperandType::Other,
            disassembled: "$t2".to_string()
        });
    }
}

pub type Abi = bindings::RabbitizerAbi;

pub fn config_set_register_fpr_abi_names(abi: Abi) {
    unsafe {
        bindings::RabbitizerConfig_Cfg.regNames.fprAbiNames = abi;
    }
}
