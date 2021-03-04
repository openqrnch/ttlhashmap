//! A HashMap-like container which keeps track of node timestamps and can decay
//! nodes by a timeout or a configured maximum number of nodes.
//!
//! There are two classes of methods to enforce constraints:
//! - Immediate removal
//! - "Split" (the "removed" nodes are returned to the caller).

use std::borrow::Borrow;
use std::collections::HashMap;
use std::hash::Hash;
use std::time::{Duration, Instant};

// ToDo:
// - Current implementation is inefficient in several ways.  There's plenty of
//   optimization to be done, in particular once HashMap::drain_filter()
//   stabilizes.
// - Make it possible to switch between SystemTime and Instant easily, and use
//   SystemTime for tests and provide a way for the application to set a
//   SystemTime.

/// Internal HashMap value which wraps the application's type in a timestamped
/// buffer.
struct ValueWrapper<V> {
  timeout: Instant,
  val: V
}

/// When to automatically run `cleanup()`.
pub enum AutoClean {
  /// Automatically run cleanup for all methods which read/write HashMap
  /// content/entries.
  Always,

  /// Automatically run cleanup for methods that write HashMap
  /// content/entries.
  Modify,

  /// Never automatically run cleanup.
  Never
}


/// Representation of decaying HashMap.
pub struct TtlHashMap<K, V>
where
  K: Eq + Hash
{
  /// Internal HashMap used to store the keys and wrapped values.
  map: HashMap<K, ValueWrapper<V>>,

  /// Default Time-To-Live for HashMap entries.
  pub ttl: Duration,

  /// Cached "oldest" cleanup timestamp.
  /// This is used to avoid having to iterate over all HashMap entries for
  /// each cleanup procedure.
  oldest: Option<Instant>,

  /// If `true` then run `cleanup()` automatically for each operation that
  /// modifies
  pub autoclean: AutoClean,

  /// Maximum number of nodes to keep.  If `None` there's no fixed limit.
  pub max_nodes: Option<usize>
}


impl<K, V> TtlHashMap<K, V>
where
  K: Eq + Hash
{
  pub fn new(ttl: Duration) -> Self {
    TtlHashMap {
      map: HashMap::new(),
      ttl,
      oldest: None,
      autoclean: AutoClean::Always,
      max_nodes: None
    }
  }


  /// If a maximum number of nodes has been set, filter out excessive nodes
  /// and return the excess.  The oldest nodes will be selected to be removed
  /// from the internal storage.
  ///
  /// ```
  /// use std::time::{Duration, Instant};
  /// use std::thread;
  /// use ttlhashmap::{TtlHashMap, AutoClean};
  ///
  /// fn main() {
  ///   let mut map = TtlHashMap::new(Duration::from_millis(100));
  ///   map.autoclean = AutoClean::Never;
  ///
  ///   map.insert("test1", "This is test1's value");
  ///   thread::sleep(Duration::from_millis(50));
  ///   map.insert("test2", "This is test2's value");
  ///   thread::sleep(Duration::from_millis(50));
  ///   map.insert("test3", "This is test3's value");
  ///
  ///   // Set the maximum number of nodes
  ///   map.max_nodes = Some(2);
  ///
  ///   assert_eq!(map.len(), 3);
  ///   let excess = map.split_by_bound();
  ///
  ///   assert_eq!(map.len(), 2);
  ///   assert_eq!(excess.len(), 1);
  ///
  ///   assert_eq!(map.contains_key("test1"), false);
  ///   assert_eq!(map.contains_key("test2"), true);
  ///   assert_eq!(map.contains_key("test3"), true);
  ///   assert_eq!(excess.contains_key("test1"), true);
  ///   assert_eq!(excess.contains_key("test2"), false);
  ///   assert_eq!(excess.contains_key("test3"), false);
  /// }
  /// ```
  pub fn split_by_bound(&mut self) -> HashMap<K, V> {
    if let Some(max) = self.max_nodes {
      self.split_by_num_bound(max)
    } else {
      HashMap::new()
    }
  }


  /// If an internal maximum number of nodes has been set, remove the excessive
  /// nodes.  The oldest nodes will be removed.
  pub fn remove_by_bound(&mut self) {
    let _ = self.split_by_bound();
  }


  /// Given a supplied maximum number of nodes, cut out the excess (ordered by
  /// age so the oldest entries are removed), and return the excess in a new
  /// HashMap.
  ///
  /// ```
  /// use std::time::{Duration, Instant};
  /// use std::thread;
  /// use ttlhashmap::{TtlHashMap, AutoClean};
  ///
  /// fn main() {
  ///   let mut map = TtlHashMap::new(Duration::from_millis(100));
  ///   map.autoclean = AutoClean::Never;
  ///
  ///   map.insert("test1", "This is test1's value");
  ///   thread::sleep(Duration::from_millis(50));
  ///   map.insert("test2", "This is test2's value");
  ///   thread::sleep(Duration::from_millis(50));
  ///   map.insert("test3", "This is test3's value");
  ///
  ///   assert_eq!(map.len(), 3);
  ///
  ///   // Explicitly pass an maximum number of nodes
  ///   let excess = map.split_by_num_bound(2);
  ///
  ///   assert_eq!(map.len(), 2);
  ///   assert_eq!(excess.len(), 1);
  ///
  ///   assert_eq!(map.contains_key("test1"), false);
  ///   assert_eq!(map.contains_key("test2"), true);
  ///   assert_eq!(map.contains_key("test3"), true);
  ///   assert_eq!(excess.contains_key("test1"), true);
  ///   assert_eq!(excess.contains_key("test2"), false);
  ///   assert_eq!(excess.contains_key("test3"), false);
  /// }
  /// ```
  pub fn split_by_num_bound(&mut self, max: usize) -> HashMap<K, V> {
    let mut stale = HashMap::new();

    if self.map.len() > max {
      let mut v = self.to_sorted_vec();

      // As long as temporary vector is longer than the limit, keep moving
      // the last entries to the output
      while v.len() > max {
        if let Some((k, v)) = v.pop() {
          stale.insert(k, v.val);
        } else {
          break;
        }
      }

      // Update the cached "oldest" timeout
      if let Some((_, v)) = v.last() {
        self.oldest = Some(v.timeout);
      } else {
        self.oldest = None;
      }

      // Move any remaining nodes back into the internal storage HashMap
      for (k, v) in v.drain(..) {
        self.map.insert(k, v);
      }
    }
    stale
  }


  /// Remove all nodes that have timed out.
  pub fn remove_by_timeout(&mut self) {
    // Only run if there's a cached "oldest entry"
    if let Some(oldest) = self.oldest {
      let now = Instant::now();

      // ... and the current time has passed that "oldest entry"
      if now > oldest {
        let mut new_oldest: Option<Instant> = None;
        self.map.retain(|_, v| {
          // Note: We're filtering out entries to keep.
          // If the current node expires in the future, then we should return
          // `true` to it is retained.
          let keep = v.timeout > now;

          // Find out which is the oldest among the future nodes.

          // If this is a future node then include it in the check.
          if keep {
            // Keep track of the oldest node (among the ones being kept
            // around).
            if let Some(no) = new_oldest {
              if v.timeout < no {
                new_oldest = Some(v.timeout);
              }
            } else {
              new_oldest = Some(v.timeout);
            }
          }
          keep
        });

        self.oldest = new_oldest;
      }
    }
  }


  /// Split out all nodes that have timed out.
  pub fn split_by_timeout(&mut self) -> HashMap<K, V> {
    let mut timedout = HashMap::new();

    // Only run if there's a cached "oldest entry"
    if let Some(oldest) = self.oldest {
      let now = Instant::now();

      // ... and the current time has passed that "oldest entry"
      if now > oldest {
        let mut new_oldest: Option<Instant> = None;

        let mut sorted = self.to_sorted_vec();

        // Keep pulling the oldest node off the list.
        while !sorted.is_empty() {
          let n = sorted.pop();
          if let Some((k, v)) = n {
            if now > v.timeout {
              // expired -- put it in the return map
              timedout.insert(k, v.val);
            } else {
              // This node happens to be the oldest of the remaining nodes
              new_oldest = Some(v.timeout);
              // hasn't expired, put it back into internal storage and break
              // out of loop
              self.map.insert(k, v);
              break;
            }
          }
        }

        // Any remaining entries belong in the internal storage
        self.vec_to_internal(sorted);

        self.oldest = new_oldest;
      }
    }

    timedout
  }


  /// Split out expired and excessive nodes.
  ///
  /// ```
  /// use std::time::{Duration, Instant};
  /// use std::thread;
  /// use ttlhashmap::{TtlHashMap, AutoClean};
  ///
  /// fn main() {
  ///   let mut map = TtlHashMap::new(Duration::from_secs(1));
  ///   map.autoclean = AutoClean::Never;
  ///
  ///   // test1 will be deleted (by expiry)
  ///   map.insert("test1", "This is test1's value");
  ///   thread::sleep(Duration::from_secs(2));
  ///   // test2 will be deleted (by maximum nodes bound)
  ///   map.insert("test2", "This is test2's value");
  ///   thread::sleep(Duration::from_millis(50));
  ///   // test3 will remain
  ///   map.insert("test3", "This is test3's value");
  ///
  ///   assert_eq!(map.len(), 3);
  ///
  ///   // Set the maximum number of nodes to 1
  ///   map.max_nodes = Some(1);
  ///
  ///   // Explicitly pass an maximum number of nodes
  ///   let excess = map.split();
  ///
  ///   assert_eq!(map.len(), 1);
  ///   assert_eq!(excess.len(), 2);
  ///
  ///   assert_eq!(map.contains_key("test1"), false);
  ///   assert_eq!(map.contains_key("test2"), false);
  ///   assert_eq!(map.contains_key("test3"), true);
  ///   assert_eq!(excess.contains_key("test1"), true);
  ///   assert_eq!(excess.contains_key("test2"), true);
  ///   assert_eq!(excess.contains_key("test3"), false);
  /// }
  /// ```
  pub fn split(&mut self) -> HashMap<K, V> {
    let mut ret = self.split_by_bound();

    for (k, v) in self.split_by_timeout() {
      ret.insert(k, v);
    }

    ret
  }


  /// Remove outdated entries and then, if a maximum number of nodes has been
  /// set, then remove the exessive nodes.
  ///
  /// ```
  /// use std::time::{Duration, Instant};
  /// use std::thread;
  /// use ttlhashmap::{TtlHashMap, AutoClean};
  ///
  /// fn main() {
  ///   let mut map = TtlHashMap::new(Duration::from_secs(1));
  ///   map.autoclean = AutoClean::Never;
  ///
  ///   // test1 will be deleted (by expiry)
  ///   map.insert("test1", "This is test1's value");
  ///   thread::sleep(Duration::from_secs(2));
  ///   // test2 will be deleted (by maximum nodes bound)
  ///   map.insert("test2", "This is test2's value");
  ///   thread::sleep(Duration::from_millis(50));
  ///   // test3 will remain
  ///   map.insert("test3", "This is test3's value");
  ///
  ///   assert_eq!(map.len(), 3);
  ///
  ///   // Set the maximum number of nodes to 1
  ///   map.max_nodes = Some(1);
  ///
  ///   // Explicitly pass an maximum number of nodes
  ///   map.cleanup();
  ///
  ///   assert_eq!(map.len(), 1);
  ///
  ///   assert_eq!(map.contains_key("test1"), false);
  ///   assert_eq!(map.contains_key("test2"), false);
  ///   assert_eq!(map.contains_key("test3"), true);
  /// }
  /// ```
  pub fn cleanup(&mut self) {
    // Only run if there's a cached "oldest entry"
    if let Some(oldest) = self.oldest {
      let now = Instant::now();

      // ... and the current time has passed that "oldest entry"
      if now > oldest {
        let mut new_oldest: Option<Instant> = None;
        //self.map.retain(|_, v| (v.timeout > now));
        self.map.retain(|_, v| {
          // Note: We're filtering out entries to keep.
          // If the current node expires in the future, then we should return
          // `true` to it is retained.
          let keep = v.timeout > now;

          // Find out which is the oldest among the future nodes.

          // If this is a future node then include it in the check.
          if keep {
            if let Some(no) = new_oldest {
              if v.timeout < no {
                new_oldest = Some(v.timeout);
              }
            } else {
              new_oldest = Some(v.timeout);
            }
          }
          keep
        });

        self.oldest = new_oldest;
      }
    }

    if let Some(max) = self.max_nodes {
      self.split_by_num_bound(max);
    }
  }

  /// If either:
  /// - The provided Instant is older than the cached oldest timestamp
  /// - There is no cached oldest timestamp
  /// .. then use the provided timestamp as the cached "oldest timestamp".
  fn update_oldest(&mut self, croaktime: Instant) {
    if let Some(oldest) = self.oldest {
      if croaktime < oldest {
        self.oldest = Some(croaktime)
      }
    } else {
      self.oldest = Some(croaktime)
    }
  }

  /// Touch an entry, if it exists.
  ///
  /// This will update the entry's timeout timestamp to the current time + the
  /// time-to-live.
  pub fn touch<Q: ?Sized>(&mut self, key: &Q)
  where
    K: Borrow<Q>,
    Q: Hash + Eq
  {
    if let Some(v) = self.map.get_mut(key) {
      let croaktime = Instant::now() + self.ttl;

      v.timeout = croaktime;

      // We could in theory do this:
      //
      //   if let None = self.oldest {
      //     self.oldest = Some(croaktime)
      //   }
      //
      // .. because since we're updating this entry it will have the latest
      // timeout, by definition.  However, this only holds true as long as ttl
      // doesn't change, or there are per-node TTL's, and this is something we
      // probably want to support.  So we'll do it this way:
      self.update_oldest(croaktime);
    }
  }


  pub fn contains_key<Q: ?Sized>(&self, key: &Q) -> bool
  where
    K: Borrow<Q>,
    Q: Hash + Eq
  {
    self.map.contains_key(key)
  }


  /// Get the requested entry, and refresh its time-to-live.
  pub fn get<Q: ?Sized>(&mut self, key: &Q) -> Option<&V>
  where
    K: Borrow<Q>,
    Q: Hash + Eq
  {
    match self.autoclean {
      AutoClean::Always => self.cleanup(),
      _ => {}
    }
    self.touch(key);
    self.get_raw(key)
  }


  pub fn get_raw<Q: ?Sized>(&self, key: &Q) -> Option<&V>
  where
    K: Borrow<Q>,
    Q: Hash + Eq
  {
    match self.map.get(key) {
      Some(v) => Some(&(v.val)),
      None => None
    }
  }

  pub fn get_mut<Q: ?Sized>(&mut self, key: &Q) -> Option<&mut V>
  where
    K: Borrow<Q>,
    Q: Hash + Eq
  {
    match self.autoclean {
      AutoClean::Always => self.cleanup(),
      _ => {}
    }
    self.touch(key);
    self.get_mut_raw(key)
  }


  pub fn get_mut_raw<Q: ?Sized>(&mut self, key: &Q) -> Option<&mut V>
  where
    K: Borrow<Q>,
    Q: Hash + Eq
  {
    match self.map.get_mut(key) {
      Some(v) => Some(&mut (v.val)),
      None => None
    }
  }


  pub fn insert(&mut self, key: K, value: V) -> Option<V> {
    match self.autoclean {
      AutoClean::Always | AutoClean::Modify => self.cleanup(),
      _ => {}
    }

    let croaktime = Instant::now() + self.ttl;
    let ret = self.map.insert(
      key,
      ValueWrapper {
        timeout: croaktime,
        val: value
      }
    );
    self.update_oldest(croaktime);

    match ret {
      Some(v) => Some(v.val),
      None => None
    }
  }


  pub fn remove<Q: ?Sized>(&mut self, key: &Q) -> Option<V>
  where
    K: Borrow<Q>,
    Q: Hash + Eq
  {
    match self.autoclean {
      AutoClean::Always | AutoClean::Modify => self.cleanup(),
      _ => {}
    }
    match self.map.remove(key) {
      Some(v) => Some(v.val),
      None => None
    }
  }


  pub fn len(&self) -> usize {
    self.map.len()
  }


  pub fn is_empty(&self) -> bool {
    self.map.is_empty()
  }


  /// Internal function used for tests.
  #[cfg(test)]
  fn set_timestamp<Q: ?Sized>(&mut self, key: &Q, ts: Instant)
  where
    K: Borrow<Q>,
    Q: Hash + Eq
  {
    if let Some(v) = self.map.get_mut(key) {
      v.timeout = ts;
    }
  }


  /// Drain all key/value pairs from internal HashMap, put them in a Vec, sort
  /// it (oldest last) and return it.
  fn to_sorted_vec(&mut self) -> Vec<(K, ValueWrapper<V>)> {
    // Move all the nodes (key and value) into a temporary vector so that it
    // can be sorted.
    let it = self.map.drain();
    let mut v: Vec<(K, ValueWrapper<V>)> = it.collect();

    // Sort in increasing age (oldest last)
    v.sort_unstable_by(|a, b| b.1.timeout.partial_cmp(&a.1.timeout).unwrap());

    v
  }


  fn vec_to_internal(&mut self, mut list: Vec<(K, ValueWrapper<V>)>) {
    for (k, v) in list.drain(..) {
      self.map.insert(k, v);
    }
  }
}


#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn single_entry() {
    let mut map = TtlHashMap::new(Duration::new(1, 0));
    assert_eq!(map.is_empty(), true);
    assert_eq!(map.len(), 0);

    map.insert("hello", "world");
    assert_eq!(map.is_empty(), false);
    assert_eq!(map.len(), 1);
    assert_eq!(map.get("hello"), Some(&"world"));

    // Entry should still exist
    map.cleanup();
    assert_eq!(map.is_empty(), false);
    assert_eq!(map.len(), 1);
    assert_eq!(map.get("hello"), Some(&"world"));

    // Wait more than 1s and cleanup again
    std::thread::sleep(Duration::new(2, 0));
    map.cleanup();

    assert_eq!(map.is_empty(), true);
    assert_eq!(map.len(), 0);
    assert_eq!(map.get("hello"), None);
  }

  #[test]
  fn two_entries() {
    let mut map = TtlHashMap::new(Duration::new(1, 0));
    assert_eq!(map.is_empty(), true);
    assert_eq!(map.len(), 0);

    map.insert("hello", "world");
    map.insert("foo", "bar");
    assert_eq!(map.is_empty(), false);
    assert_eq!(map.len(), 2);
    assert_eq!(map.get("hello"), Some(&"world"));
    assert_eq!(map.get("foo"), Some(&"bar"));

    // Entry should still exist
    map.cleanup();
    assert_eq!(map.is_empty(), false);
    assert_eq!(map.len(), 2);
    assert_eq!(map.get("hello"), Some(&"world"));
    assert_eq!(map.get("foo"), Some(&"bar"));

    // Wait more than 1s and cleanup again
    std::thread::sleep(Duration::new(2, 0));
    map.cleanup();

    assert_eq!(map.is_empty(), true);
    assert_eq!(map.len(), 0);
    assert_eq!(map.get("hello"), None);
    assert_eq!(map.get("foo"), None);
  }
}

// vim: set ft=rust et sw=2 ts=2 sts=2 cinoptions=2 tw=79 :
