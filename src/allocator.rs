/*use memmap2::{MmapMut, MmapOptions};

pub struct Allocator {
    memory_start: *mut u8,
    memory_end: *mut u8,
    // the map is dropped when the allocator is dropped
    mmap: Option<MmapMut>,
}

#[repr(C)]
struct BlockHeader {
    /// 0 for normal blocks, 1 for the final block
    status: u8,
    _pad: [u8; 3],
    /// Magic number (for debugging), should be 0x4A21
    checknum: u16,
    /// For garbage collection
    mark: u8,
    /// (0=free, 1=used)
    used: u8,
    /// 0 for the first block
    prev_size: u32,
    size: u32,
}

const _: [(); 16] = [(); std::mem::size_of::<BlockHeader>()];

#[repr(transparent)]
#[derive(Clone, Copy)]
struct BlockPtr(*mut BlockHeader);

impl BlockPtr {
    fn from(ptr: *mut u8) -> Self {
        Self(ptr as *mut BlockHeader)
    }

    fn init(&self, size: u32, prev_size: u32, tail: bool) {
        unsafe {
            (*self.0).status = tail as u8;
            (*self.0).checknum = 0x4A21;
            (*self.0).mark = 0;
            (*self.0).used = 0;
            (*self.0).prev_size = prev_size;
            (*self.0).size = size;
        }
    }

    fn validate(&self, a: Option<&Allocator>) {
        debug_assert!(self.0 as usize % 8 == 0); // alignment
        if let Some(a) = a {
            debug_assert!(self.0 as usize >= a.memory_start as usize);
            debug_assert!((self.0 as usize) < a.memory_end as usize);
        }
        debug_assert!(unsafe { (*self.0).checknum } == 0x4A21);
        debug_assert!(unsafe { (*self.0).size } % 8 == 0);
        debug_assert!(unsafe { (*self.0).prev_size } % 8 == 0);
    }

    fn next(&self) -> Self {
        if self.is_tail() { panic!() }
        Self(unsafe { self.0.byte_add((*self.0).size as usize) })
    }

    fn prev(&self) -> Self {
        if self.is_head() { panic!() }
        Self(unsafe { self.0.byte_sub((*self.0).prev_size as usize) })
    }

    fn is_head(&self) -> bool {
        unsafe { (*self.0).prev_size == 0 }
    }

    fn is_tail(&self) -> bool {
        unsafe { (*self.0).status == 1 }
    }

    fn print_info(&self) {
        fn fmt_num(n: u32) -> String {
            if n >= 1_000_000 {
                format!("{:>5.1}M", n as f64 / 1_000_000.0)
            } else if n >= 1_000 {
                format!("{:>5.1}K", n as f64 / 1_000.0)
            } else {
                format!("{:>5} ", n)
            }
        }

        println!("{:p} {:>5} {}{}{}",
            self.0, 
            fmt_num(unsafe { (*self.0).size }),
            if unsafe { (*self.0).used } == 1 { "U" } else { " " },
            if unsafe { (*self.0).mark } == 1 { "M" } else { " " },
            if unsafe { (*self.0).status } == 1 { "T" } else if unsafe { (*self.0).prev_size } == 0 { "H" } else { "" },
        );
    }

    fn split(&self, size_first: u32) -> (Self, Self) { unsafe {
        debug_assert!(size_first % 8 == 0);
        debug_assert!((*self.0).size >= size_first + 16);
        debug_assert!((*self.0).used == 0, "splitting a used block");
        let size_second = (*self.0).size - size_first - 16;
        (*self.0).size = size_first;
        let second = BlockPtr(self.0.byte_add(size_first as usize)); 
        second.init(size_second, size_first, false);
        if (*self.0).status == 1 {
            (*self.0).status = 0;
            (*second.0).status = 1;
        }
        (*self, second)
    } }

    fn content_ptr(&self) -> *mut u8 {
        unsafe { (self.0 as *mut u8).add(16) }
    }

    fn size(&self) -> u32 { unsafe { (*self.0).size } }

    fn is_free(&self) -> bool { unsafe { (*self.0).used == 0 } }

    fn set_used(&self, used: bool) { unsafe { (*self.0).used = used as u8 } }
}

impl Allocator {
    pub unsafe fn new(memory_start: *mut u8, memory_end: *mut u8) -> Self {
        let mut allocator = Self { memory_start, memory_end, mmap: None };
        allocator.init();
        allocator
    }

    pub fn new_mmap(size: usize) -> std::io::Result<Self> {
        let mut mmap = MmapOptions::new().len(size).map_anon()?;
        let range = mmap.as_mut_ptr_range();
        let mut self_ = unsafe { Self::new(range.start, range.end) };
        self_.mmap = Some(mmap);
        Ok(self_)
    }

    fn init(&self) {
        debug_assert!(self.memory_start as usize % 16 == 0);
        debug_assert!(self.memory_end as usize % 16 == 0);
        let memory_size = self.memory_end as usize - self.memory_start as usize;
        debug_assert!(memory_size > 16);
        debug_assert!(memory_size < u32::MAX as usize);
        self.head().init(memory_size as u32, 0, true);
    }

    fn head(&self) -> BlockPtr {
        BlockPtr::from(self.memory_start)
    }

    pub fn dump_debug(&self) {
        let mut block = self.head();
        loop {
            block.validate(Some(self));
            block.print_info();
            if block.is_tail() { break }
            block = block.next();
        }
    }

    pub fn alloc(&self, size: usize) -> Option<*mut u8> {
        let size = (size + 15) & !15; // should we align to 8 or 16?
        assert!(size < u32::MAX as usize);
        // walk the blocks looking for a free one
        let mut block = self.head();
        loop {
            if block.is_free() && block.size() >= (size as u32) {
                let (alloc_block, _) = block.split(size as u32);
                alloc_block.set_used(true);
                return Some(alloc_block.content_ptr());
            }
            if block.is_tail() { break }
            block = block.next();
        }
        None
    }
}*/