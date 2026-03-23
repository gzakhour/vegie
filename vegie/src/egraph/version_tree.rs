pub type Version = usize;

#[derive(Debug, Clone)]
pub struct VersionNode {
  superversion: Version,
  subversions: Vec<Version>,
  exist: bool,
}

#[derive(Debug, Clone)]
pub struct VersionTree {
  versions: Vec<VersionNode>,
  removed_versions: Vec<Version>,
}

impl VersionTree {
  pub const ROOT_VERSION: Version = 0;

  pub fn new() -> VersionTree {
    let root = VersionNode {
      superversion: VersionTree::ROOT_VERSION,
      subversions: Vec::new(),
      exist: true,
    };
    VersionTree { versions: vec![root], removed_versions: Vec::new() }
  }

  pub fn path(&self, v: Version) -> Vec<Version> {
    let mut path = vec![v];
    self.ancestors(v).for_each(|sv| path.push(sv));
    path
  }

  pub fn branchout(&mut self, v: Version) -> Version {
    assert!(self.exists(v), "Cannot branchout from removed version: version {v}",);
    let new_version = VersionNode { superversion: v, subversions: Vec::new(), exist: true };
    let new_version_id = match self.removed_versions.pop() {
      Some(recycled_id) => {
        self.versions[recycled_id] = new_version;
        recycled_id
      },
      None => {
        let new_id = self.versions.len();
        self.versions.push(new_version);
        new_id
      },
    };
    self.versions[v].subversions.push(new_version_id);
    new_version_id
  }

  pub fn remove(&mut self, v: Version) {
    assert!(v != VersionTree::ROOT_VERSION, "Cannot remove the root version.");
    assert!(self.exists(v), "Cannot remove already removed version: version {v}.",);
    for sv in 0..self.versions[v].subversions.len() {
      self.remove_version(self.versions[v].subversions[sv]);
    }
    let parent = self.versions[v].superversion;
    self.versions[parent].subversions.retain(|&sv| sv != v);
    self.remove_version(v);
  }

  pub fn remove_version(&mut self, version: Version) {
    let node = &mut self.versions[version];
    node.subversions.clear();
    node.exist = false;
    self.removed_versions.push(version);
  }

  pub fn rebase(&mut self, v: Version, new_parent: Version) {
    assert!(v != VersionTree::ROOT_VERSION, "Cannot rebase the root version.");
    assert!(self.exists(v), "Cannot rebase removed version: version {v}.");
    assert!(self.exists(new_parent), "Cannot rebase to removed version: version {new_parent}.");
    let parent = self.versions[v].superversion;
    if parent != new_parent {
      self.versions[parent].subversions.retain(|&sv| sv != v);
      self.versions[v].superversion = new_parent;
      self.versions[new_parent].subversions.push(v);
    }
  }

  pub fn versions(&self) -> std::ops::Range<Version> {
    0..self.versions.len()
  }

  pub fn superversion(&self, v: Version) -> Version {
    assert!(self.exists(v), "Cannot query superversion of removed version: version {v}",);
    self.versions[v].superversion
  }

  pub fn subversions(&self, v: Version) -> &Vec<Version> {
    assert!(self.exists(v), "Cannot query subversions of removed version: version {v}",);
    &self.versions[v].subversions
  }

  pub fn ancestors(&self, version: Version) -> impl std::iter::Iterator<Item = Version> + '_ {
    pub struct AncestorIter<'a> {
      vt: &'a VersionTree,
      current: Version,
    }

    impl Iterator for AncestorIter<'_> {
      type Item = Version;
      fn next(&mut self) -> Option<Self::Item> {
        let superversion = self.vt.superversion(self.current);
        if self.current == superversion {
          return None;
        }
        self.current = superversion;
        Some(superversion)
      }
    }

    AncestorIter { vt: self, current: version }
  }

  pub fn descendants(&self, version: Version) -> impl std::iter::Iterator<Item = Version> + '_ {
    pub struct DescendantIter<'a> {
      vt: &'a VersionTree,
      stack: Vec<Version>,
    }

    impl Iterator for DescendantIter<'_> {
      type Item = Version;
      fn next(&mut self) -> Option<Self::Item> {
        let current_option = self.stack.pop();
        if let Some(current) = current_option {
          for &child in &self.vt.versions[current].subversions {
            self.stack.push(child);
          }
          current_option
        } else {
          None
        }
      }
    }

    DescendantIter { vt: self, stack: self.versions[version].subversions.clone() }
  }

  #[inline(always)]
  pub fn exists(&self, v: Version) -> bool {
    self.versions[v].exist
  }
}

