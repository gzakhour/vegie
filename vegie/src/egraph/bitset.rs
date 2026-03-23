type Block = usize;
const BLOCK_BITS: usize = Block::BITS as usize;

#[derive(Debug, Clone, Default)]
pub struct BitSet {
  // TODO consider making this an BTreeMap<BlockIndex, Block> instead of a Vec<Block>:
  //    reduces memory consumption and traversing may be faster, but search becomes log(n)
  underlying: Vec<Block>,
  size: usize,
}

impl BitSet {
  pub fn size(&self) -> usize {
    self.size
  }

  pub fn blocks(&self) -> usize {
    self.underlying.len()
  }

  pub fn add(&mut self, x: usize) -> bool {
    let (block, index) = (x / BLOCK_BITS, x % BLOCK_BITS);
    if block >= self.underlying.len() {
      self.underlying.resize(block * 2 + 16, 0);
    }
    let mask = 1 << index;
    let block_before = self.underlying[block];
    self.underlying[block] |= mask;
    if block_before != self.underlying[block] {
      self.size += 1;
      return true;
    }
    false
  }

  #[inline(always)]
  pub fn contains(&self, x: usize) -> bool {
    let block = x / BLOCK_BITS;
    match self.underlying.get(block) {
      Some(block) => {
        let index = x % BLOCK_BITS;
        (block & (1 << index)) != 0
      },
      None => false,
    }
  }

  pub fn remove(&mut self, x: usize) -> bool {
    let (block, index) = (x / BLOCK_BITS, x % BLOCK_BITS);
    if block >= self.underlying.len() {
      return false;
    }
    let mask = Block::MAX ^ (1 << index);
    let block_before = self.underlying[block];
    self.underlying[block] &= mask;
    if block_before != self.underlying[block] {
      self.size -= 1;
      return true;
    }
    false
  }

  pub fn clear(&mut self) {
    self.underlying.clear();
    self.size = 0;
  }

  pub fn iter(&self) -> impl std::iter::Iterator<Item = usize> + '_ {
    let mut iter = self.underlying.iter();
    let head_block = iter.next().cloned().unwrap_or_default();
    BitSetIterator { blocks: iter, block: head_block, base: 0 }
  }
}

struct BitSetIterator<'a> {
  blocks: std::slice::Iter<'a, Block>,
  block: Block,
  base: usize,
}

impl Iterator for BitSetIterator<'_> {
  type Item = usize;

  #[inline]
  fn next(&mut self) -> Option<Self::Item> {
    loop {
      if self.block != 0 {
        let skip = self.block.trailing_zeros() as usize;
        self.block &= self.block - 1;
        return Some(self.base + skip);
      }
      let next_block = self.blocks.next()?;
      self.block = *next_block;
      self.base += BLOCK_BITS;
    }
  }
}

