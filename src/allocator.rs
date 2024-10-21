use std::cell::Cell;

use memmap2::{MmapMut, MmapOptions};

pub struct Allocator {
    memory_start: *mut u8,
    memory_end: *mut u8,
    // the map is dropped when the allocator is dropped
    mmap: Option<MmapMut>,
    is_init: Cell<bool>,
}

bitflags::bitflags! {
    struct BlkStatus: u8 {
        const TAIL = 0b01;
        const USED = 0b10;
    }
}

#[repr(C)]
struct BlockHeader {
    /// 0 for normal blocks, 1 for the final block
    status: BlkStatus,
    /// Magic number (for debugging), should be 0x[12,4A,21]
    checknum: [u8; 3],
    /// XOR of size and prev_size
    /// `size` does NOT include the header
    xor_size: u32,
    _pad: [u8; 4],
    refcount: u32,
}

const _: [(); 16] = [(); std::mem::size_of::<BlockHeader>()];

#[repr(transparent)]
#[derive(Clone, Copy)]
struct BlockPtr(*mut BlockHeader);

impl BlockPtr {
    fn from(ptr: *mut u8) -> Self {
        Self(ptr as *mut BlockHeader)
    }

    fn from_content_ptr(ptr: *mut u8) -> Self {
        Self(unsafe { ptr.sub(16) } as *mut BlockHeader)
    }

    fn init(&self, size: u32, prev_size: u32, tail: bool) {
        unsafe {
            (*self.0).status = if tail { BlkStatus::TAIL } else { BlkStatus::empty() };
            (*self.0).checknum = [0x12, 0x4A, 0x21];
            (*self.0).xor_size = size ^ prev_size;
            (*self.0).refcount = 0;
        }
    }

    fn validate(&self, a: Option<&Allocator>) {
        debug_assert!(self.0 as usize % 8 == 0); // alignment
        if let Some(a) = a {
            debug_assert!(self.0 as usize >= a.memory_start as usize);
            debug_assert!((self.0 as usize) < a.memory_end as usize);
        }
        debug_assert!(unsafe { (*self.0).checknum } == [0x12, 0x4A, 0x21]);
        debug_assert!(unsafe { (*self.0).xor_size } % 8 == 0);
    }

    /// Return the block pointer and its size
    fn next(&self, size: u32) -> (Self, u32) {
        if self.is_tail() { panic!() }
        let ptr = Self(unsafe { self.0.byte_add(size as usize + 16) });
        let s = unsafe { (*ptr.0).xor_size ^ size };
        (ptr, s)
    }

    /// Return the block pointer and its size
    fn prev(&self, size: u32) -> (Self, u32) {
        if self.is_head(size) { panic!() }
        let s = self.prev_size(size);
        let ptr = Self(unsafe { self.0.byte_sub(s as usize + 16) });
        (ptr, s)
    }

    fn prev_size(&self, size: u32) -> u32 {
        unsafe { (*self.0).xor_size ^ size }
    }

    fn is_head(&self, size: u32) -> bool {
        self.prev_size(size) == 0
    }

    fn is_tail(&self) -> bool {
        unsafe { (*self.0).status.contains(BlkStatus::TAIL) }
    }

    fn is_used(&self) -> bool {
        unsafe { (*self.0).status.contains(BlkStatus::USED) }
    }

    fn print_info(&self, size: u32) {
        fn fmt_num(n: u32) -> String {
            if n >= 1_000_000 {
                format!("{:>5.1}M", n as f64 / 1_000_000.0)
            } else if n >= 1_000 {
                format!("{:>5.1}K", n as f64 / 1_000.0)
            } else {
                format!("{:>5} ", n)
            }
        }

        print!("{:p} {:>5} {}{}",
            self.0, 
            fmt_num(size),
            if self.is_used() { "U" } else { " " },
            //if unsafe { (*self.0).mark } == 1 { "M" } else { " " },
            if self.is_tail() { "T" } else if self.is_head(size) { "H" } else { " " });
        if self.get_refcount() > 0 {
            print!("   ({} refs)", self.get_refcount())
        }
        println!()
    }

    fn split(&self, this_size: u32, size_first: u32) -> (Self, Self) { unsafe {
        debug_assert!(size_first % 8 == 0);
        debug_assert!(this_size >= size_first + 32);
        debug_assert!(!self.is_used(), "splitting a used block");
        let size_second = this_size - size_first - 16;
        (*self.0).xor_size ^= this_size ^ size_first;
        let second = BlockPtr(self.0.byte_add(size_first as usize + 16));
        second.init(size_second, size_first, false);
        if self.is_tail() {
            (*self.0).status.remove(BlkStatus::TAIL);
            (*second.0).status.insert(BlkStatus::TAIL);
        }
        (*self, second)
    } }

    fn content_ptr(&self) -> *mut u8 {
        unsafe { (self.0 as *mut u8).add(16) }
    }

    fn is_free(&self) -> bool { !self.is_used() }

    fn set_used(&self, used: bool) { unsafe { (*self.0).status.set(BlkStatus::USED, used); } }

    /// Get the size of this block. Only valid if this is the first block which the allocator has to guarantee
    unsafe fn get_size_if_head(&self) -> u32 {
        (*self.0).xor_size // ^ 0
    }

    fn get_refcount(&self) -> u32 { unsafe { (*self.0).refcount } }
    fn inc_refcount(&self) { unsafe { (*self.0).refcount += 1; } }
    fn dec_refcount(&self) { unsafe { (*self.0).refcount -= 1; } }
}

impl Allocator {
    pub const unsafe fn new(memory_start: *mut u8, memory_end: *mut u8) -> Self {
        Self { memory_start, memory_end, mmap: None, is_init: Cell::new(false) }
    }

    pub fn new_mmap(size: usize) -> std::io::Result<Self> {
        let mut mmap = MmapOptions::new().len(size).map_anon()?;
        let range = mmap.as_mut_ptr_range();
        let mut self_ = unsafe { Self::new(range.start, range.end) };
        self_.mmap = Some(mmap);
        Ok(self_)
    }

    pub fn init(&self) {
        assert!(!self.is_init.get());
        debug_assert!(self.memory_start as usize % 16 == 0);
        debug_assert!(self.memory_end as usize % 16 == 0);
        let memory_size = self.memory_end as usize - self.memory_start as usize;
        debug_assert!(memory_size > 16);
        debug_assert!(memory_size < u32::MAX as usize);
        BlockPtr::from(self.memory_start).init(memory_size as u32, 0, true);
        self.is_init.set(true);
    }

    fn head(&self) -> (BlockPtr, u32) {
        let ptr = BlockPtr::from(self.memory_start);
        (ptr, unsafe { ptr.get_size_if_head() })
    }

    pub fn dump_debug(&self) {
        debug_assert!(self.is_init.get());
        let (mut block, mut block_size) = self.head();
        loop {
            block.validate(Some(self));
            block.print_info(block_size);
            if block.is_tail() { break }
            (block, block_size) = block.next(block_size);
        }
    }

    pub fn alloc(&self, alloc_size: usize) -> Option<*mut u8> {
        debug_assert!(self.is_init.get());
        let alloc_size = (alloc_size + 15) & !15; // round to 16
        assert!(alloc_size < u32::MAX as usize);
        // walk the blocks looking for a free one
        let (mut block, mut block_size) = self.head();
        loop {
            if block.is_free() && block_size >= (alloc_size as u32) {
                let (alloc_block, _) = block.split(block_size, alloc_size as u32);
                alloc_block.set_used(true);
                return Some(alloc_block.content_ptr());
            }
            if block.is_tail() { break }
            (block, block_size) = block.next(block_size);
        }
        None
    }

    pub fn dealloc_cheap(&self, alloc_ptr: *mut u8, _alloc_size: usize) {
        // just mark as unused, do nothing else
        BlockPtr::from_content_ptr(alloc_ptr).set_used(false);
    }

    /// Safety: the pointer must have been allocated by this allocator
    pub unsafe fn inc_refcount(ptr: *mut u8) {
        let block = BlockPtr::from_content_ptr(ptr);
        block.inc_refcount();
    }
    
    /// Safety: the pointer must have been allocated by this allocator
    pub unsafe fn dec_and_read_refcount(ptr: *mut u8) -> u32 {
        let block = BlockPtr::from_content_ptr(ptr);
        block.dec_refcount();
        block.get_refcount()
    }
}

unsafe impl std::marker::Send for Allocator {}