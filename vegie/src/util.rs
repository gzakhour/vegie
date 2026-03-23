pub fn cartesian(i: usize, j: usize) -> impl Iterator<Item=(usize, usize)> {
  struct Iter {
    max0: usize,
    max1: usize,
    i: usize, j: usize,
  }
  impl Iterator for Iter {
    type Item = (usize, usize);
    fn next(&mut self) -> Option<Self::Item> {
      if self.i >= self.max0 { return None; }
      let ans = (self.i, self.j);
      self.j += 1;
      if self.j >= self.max1 {
        self.j = 0;
        self.i += 1;
      }
      Some(ans)
    }
  }
  Iter { max0: i, max1: j, i: 0, j: 0 }
}

