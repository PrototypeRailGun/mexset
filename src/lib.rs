use std::hash::Hash;
use rustc_hash::FxHashSet;
use std::collections::BTreeSet;
use std::collections::hash_set::{ Iter, IntoIter };
use std::iter::FromIterator;
use num::traits::Unsigned;
use num::Num;


/// The MexSet data structure is an implementation of a set that can quickly find **MEX**.
/// 
/// *The MEX (Minimum EXcluded) of a subset of the set of natural numbers is the minimum natural number missing from this subset.
/// That is, it is the minimum value of the [complement](https://en.wikipedia.org/wiki/Complement_(set_theory)) set.*
/// 
/// # Examples
///
/// ```
/// use mexset::MexSet;
///
/// let mut set: MexSet<u32> = MexSet::new();
/// assert_eq!(set.minimum_excluded(), 0);   // The MEX of an empty set is 0
///
/// set.insert(2); 
/// set.insert(1);
/// assert_eq!(set.minimum_excluded(), 0);   // 0 is the smallest missing number
///
/// set.insert(0);
/// assert_eq!(set.minimum_excluded(), 3);   // mex({0, 1, 2}) = 3
///
/// set.insert(4);
/// assert_eq!(set.minimum_excluded(), 3);   // mex({0, 1, 2, 4}) = 3
///
/// set.insert(3);
/// assert_eq!(set.minimum_excluded(), 5);   // mex({0, 1, 2, 3, 4}) = 5
///
/// set.remove(&1);
/// assert_eq!(set.minimum_excluded(), 1);  // mex({0, 2, 3, 4}) = 1
/// ```
///
/// The `insert`, `remove` and `minimum_excluded` methods have a runtime of **O(log(N))**, 
/// where **N** is the number of elements in the MexSet.
///
/// If you are interested in learning more about MEX, I suggest you watch this 
/// [video](https://www.youtube.com/watch?v=JDuVLyKn7Yw).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MexSet<T: Ord + Hash + Copy + Unsigned + Num> {
    set: FxHashSet<T>,
    complement: BTreeSet<T>,
    mex_upper_bound: T,
}


impl<T: Ord + Hash + Copy + Unsigned + Num> MexSet<T> {
    /// Create new MexSet.
    ///
    /// # Examples
    ///
    /// ```
    /// use mexset::MexSet;
    /// 
    /// let set: MexSet<u32> = MexSet::new();
    /// ```
    #[inline]
    pub fn new() -> Self {
        let mut compl: BTreeSet<T> = BTreeSet::new();
        compl.insert(T::zero());
        // let s: HashSet::<T, BuildHasherDefault<NoHashHasher<T>>> = HashSet::with_hasher(BuildHasherDefault::default());
        MexSet {
            set: FxHashSet::default(),
            complement: compl,
            mex_upper_bound: T::zero(),
        }
    }
    
    /// Get the number of unique elements in a set.
    ///
    /// # Examples
    ///
    /// ```
    /// use mexset::MexSet;
    ///
    /// let mut set: MexSet<u32> = MexSet::new();
    /// assert_eq!(set.len(), 0);
    /// 
    /// set.insert(1);
    /// set.insert(1);
    /// set.insert(2);
    /// assert_eq!(set.len(), 2);
    /// ```
    #[inline]
    pub fn len(&self) -> usize {
        self.set.len()
    }

    /// Returns `true` if the set contains no elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use mexset::MexSet;
    ///
    /// let mut set: MexSet<u32> = MexSet::new();
    /// assert!(set.is_empty());
    ///
    /// set.insert(1);
    /// assert!(!set.is_empty());
    /// ```
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.mex_upper_bound.is_zero()
    }
    
    /// Clear the MexSet.
    ///
    /// # Examples
    ///
    /// ```
    /// use mexset::MexSet;
    ///
    /// let mut set: MexSet<u32> = MexSet::new();
    /// set.insert(1);
    /// set.insert(2);
    /// set.insert(3);
    ///
    /// set.clear();
    /// assert_eq!(set.len(), 0);
    #[inline]
    pub fn clear(&mut self) {
        *self = MexSet::new();
    }

    /// Adds a value to the set.
    ///
    /// If the set did not have this value present, `true` is returned.
    ///
    /// If the set did have this value present, `false` is returned.
    /// 
    /// # Examples
    ///
    /// ```
    /// use mexset::MexSet;
    /// 
    /// let mut set: MexSet<u32> = MexSet::new();
    ///
    /// assert!(set.insert(1));
    /// assert!(!set.insert(1));
    /// assert_eq!(set.len(), 1);
    /// ```
    #[inline]
    pub fn insert(&mut self, item: T) -> bool {
        if self.set.insert(item) {
            self.complement.remove(&item);
            self.mex_upper_bound = self.mex_upper_bound + T::one();
            if !self.set.contains(&self.mex_upper_bound) {
                self.complement.insert(self.mex_upper_bound);
            }
            return true;
        }

        false
    }
    
    /// Find set's MEX.
    ///
    /// # Examples
    ///
    /// ```
    /// use mexset::MexSet;
    ///
    /// let mut set: MexSet<u32> = MexSet::new();
    /// assert_eq!(set.minimum_excluded(), 0);   // { }
    /// 
    /// set.extend(vec![0, 1, 2].into_iter());
    /// assert_eq!(set.minimum_excluded(), 3);   // {0, 1, 2, _ }
    ///
    /// set.extend(vec![4, 5].into_iter());
    /// assert_eq!(set.minimum_excluded(), 3);   // {0, 1, 2, _ , 4, 5}
    ///
    /// set.insert(3);
    /// assert_eq!(set.minimum_excluded(), 6);   // {0, 1, 2, 3, 4, 5, _ }
    #[inline]
    pub fn minimum_excluded(&self) -> T {
        *self.complement.iter().next().unwrap()
    }

    /// Returns true if the set contains a value.
    ///
    /// # Examples
    ///
    /// ```
    /// use mexset::MexSet;
    ///
    /// let mut set: MexSet<u32> = MexSet::new();
    /// assert!(!set.contains(&1));
    ///
    /// set.insert(1);
    /// assert!(set.contains(&1));
    /// ```
    #[inline]
    pub fn contains(&self, value: &T) -> bool {
        self.set.contains(value)
    }

    /// Removes a value from the set. Returns whether the value was
    /// present in the set.
    ///
    /// # Examples
    ///
    /// ```
    /// use mexset::MexSet;
    ///
    /// let mut set: MexSet<u32> = MexSet::new();
    ///
    /// set.insert(1);
    /// assert_eq!(set.remove(&1), true);
    /// assert_eq!(set.remove(&1), false);
    /// ```
    #[inline]
    pub fn remove(&mut self, value: &T) -> bool {
        if self.set.remove(value) {
            if *value < self.mex_upper_bound {
                self.complement.insert(*value);
                self.mex_upper_bound = self.mex_upper_bound - T::one();
            }

            return true;
        }

        false
    }

    /// An iterator visiting all elements in arbitrary order.
    /// The iterator element type is `&'a T`.
    ///
    /// # Examples
    ///
    /// ```
    /// use mexset::MexSet;
    /// use std::collections::HashSet;
    ///
    /// let mut set: MexSet<u32> = MexSet::new();
    /// set.insert(1);
    /// set.insert(2);
    ///
    /// assert_eq!(
    ///     set.iter().collect::<HashSet<&u32>>(),
    ///     vec![&1, &2].into_iter().collect::<HashSet<&u32>>(),
    /// );
    /// ```
    #[inline]
    pub fn iter(&self) -> Iter<'_, T> {
        self.set.iter()
    }
    
    /// Create a MexSet with elements [0; n).
    ///
    /// This function is a much faster alternative to sequential `insert()` calls.
    ///
    /// # Examples
    ///
    /// ```
    /// use mexset::MexSet;
    ///
    /// assert_eq!(
    ///   MexSet::<u32>::with_range(5),
    ///   vec![0, 1, 2, 3, 4].into_iter().collect::<MexSet<u32>>(),
    /// );
    /// ```
    pub fn with_range(n: T) -> Self {
        let mut elements = FxHashSet::default();
        let mut x = T::zero();
        while x < n {
            elements.insert(x);
            x = x + T::one();
        }

        MexSet {
            set: elements,
            complement: BTreeSet::from_iter(vec![n].into_iter()),
            mex_upper_bound: n,
        }
    }
}


impl<T: Ord + Hash + Copy + Unsigned + Num> IntoIterator for MexSet<T> {
    type Item = T;
    type IntoIter = IntoIter<T>;
    
    /// Creates a consuming iterator, that is, one that moves each value out of the set in arbitrary order. 
    /// The set cannot be used after calling this.
    ///
    /// # Examples
    ///
    /// ```
    /// use mexset::MexSet;
    /// use std::collections::HashSet;
    ///
    /// let mut set: MexSet<u32> = MexSet::new();
    /// set.insert(1);
    /// set.insert(2);
    ///
    /// assert_eq!(
    ///     set.into_iter().collect::<HashSet<u32>>(),
    ///     vec![1, 2].into_iter().collect::<HashSet<u32>>(),
    /// );
    /// ```
    #[inline]
    fn into_iter(self) -> IntoIter<T> {
        self.set.into_iter()
    }
}


impl<T: Ord + Hash + Copy + Unsigned + Num> Extend<T> for MexSet<T> {
    /// Extend the MexSet with elements from an iterator.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use mexset::MexSet;
    /// 
    /// let mut set: MexSet<u32> = MexSet::new();
    /// set.extend(vec![2, 3, 5].into_iter());
    ///
    /// assert!(set.contains(&2));
    /// assert!(set.contains(&3));
    /// assert!(set.contains(&5));
    /// ```
    fn extend<I: IntoIterator<Item=T>>(&mut self, iter: I) {
        iter.into_iter().for_each(move |elem| { 
            self.insert(elem); 
        });
    }
}


impl<T: Ord + Hash + Copy + Unsigned + Num> FromIterator<T> for MexSet<T> {
    /// Сreating a MexSet from an iterator. 
    /// 
    /// # Examples
    /// 
    /// ```
    /// use mexset::MexSet;
    /// use std::iter::FromIterator;
    /// 
    /// let set: MexSet<u32> = MexSet::from_iter(vec![2, 3, 5].into_iter());
    /// assert!(set.contains(&2));
    /// assert!(set.contains(&3));
    /// assert!(set.contains(&5));
    /// 
    /// let set: MexSet<u32> = vec![5, 3, 2].into_iter().collect();
    /// assert!(set.contains(&2));
    /// assert!(set.contains(&3));
    /// assert!(set.contains(&5));
    /// ```
    #[inline]
    fn from_iter<I: IntoIterator<Item=T>>(iter: I) -> Self {
        let mut mexset = MexSet::new();
        mexset.extend(iter);
        mexset
    }
}


#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashSet;
    #[test]
    fn basics() {
        // Testing for new() and minimum_excluded() on an empty set.
        let mut mex = MexSet::<u32>::new();
        assert_eq!(mex.minimum_excluded(), 0);
        assert_eq!(mex.len(), 0);

        // Testing for insert() and size().
        assert!(mex.insert(1));
        assert_eq!(mex.minimum_excluded(), 0);
        assert_eq!(mex.len(), 1);

        assert!(mex.insert(2));
        assert_eq!(mex.minimum_excluded(), 0);
        assert_eq!(mex.len(), 2);

        assert!(mex.insert(0));
        assert_eq!(mex.minimum_excluded(), 3);
        assert_eq!(mex.len(), 3);

        assert!(mex.insert(4));
        assert_eq!(mex.minimum_excluded(), 3);
        assert_eq!(mex.len(), 4);

        assert!(mex.insert(7));
        assert_eq!(mex.minimum_excluded(), 3);
        assert_eq!(mex.len(), 5);

        assert!(mex.insert(3));
        assert_eq!(mex.minimum_excluded(), 5);
        assert_eq!(mex.len(), 6);

        assert!(!mex.insert(4));
        assert_eq!(mex.minimum_excluded(), 5);
        assert_eq!(mex.len(), 6);

        assert!(!mex.insert(4));
        assert_eq!(mex.minimum_excluded(), 5);
        assert_eq!(mex.len(), 6);

        assert!(mex.insert(40));
        assert_eq!(mex.minimum_excluded(), 5);
        assert_eq!(mex.len(), 7);

        // Testing for contains().
        assert!(mex.contains(&2));
        assert!(mex.contains(&0));
        assert!(mex.contains(&7));
        assert!(!mex.contains(&15));
        
        // Testing for clear().
        mex.clear();
        assert_eq!(mex.minimum_excluded(), 0);
        assert!(!mex.contains(&2));
        assert!(!mex.contains(&0));
    }
    
    #[test]
    fn test_extend_and_remove() {
        let mut mex: MexSet<u32> = MexSet::new();
        mex.extend(vec![5, 5, 5, 2, 4, 7, 2, 3, 4, 5, 5, 5, 6, 7].into_iter());

        assert_eq!(mex.len(), 6);
        assert_eq!(mex.minimum_excluded(), 0);

        mex.extend(vec![0, 0, 1].into_iter());
        assert_eq!(mex.len(), 8);
        assert_eq!(mex.minimum_excluded(), 8);

        mex.extend(vec![9, 8, 9]);
        assert_eq!(mex.len(), 10);
        assert_eq!(mex.minimum_excluded(), 10);

        assert!(mex.remove(&5));
        assert_eq!(mex.len(), 9);
        assert_eq!(mex.minimum_excluded(), 5);

        assert!(!mex.remove(&5));
        assert_eq!(mex.len(), 9);
        assert_eq!(mex.minimum_excluded(), 5);

        assert!(mex.remove(&4));
        assert_eq!(mex.len(), 8);
        assert_eq!(mex.minimum_excluded(), 4);

        assert!(mex.remove(&2));
        assert_eq!(mex.len(), 7);
        assert_eq!(mex.minimum_excluded(), 2);

        mex.extend(vec![5, 4, 4, 2, 5].into_iter());
        assert_eq!(mex.len(), 10);
        assert_eq!(mex.minimum_excluded(), 10);

        assert!(!mex.remove(&10));
        assert_eq!(mex.len(), 10);
        assert_eq!(mex.minimum_excluded(), 10);

        assert!(!mex.remove(&30));
        assert_eq!(mex.len(), 10);
        assert_eq!(mex.minimum_excluded(), 10);

        assert!(mex.remove(&7));
        assert_eq!(mex.len(), 9);
        assert_eq!(mex.minimum_excluded(), 7);

        assert!(mex.remove(&9));
        assert_eq!(mex.len(), 8);
        assert_eq!(mex.minimum_excluded(), 7);

        assert!(mex.remove(&8));
        assert_eq!(mex.len(), 7);
        assert_eq!(mex.minimum_excluded(), 7);

        assert!(mex.remove(&6));
        assert_eq!(mex.len(), 6);
        assert_eq!(mex.minimum_excluded(), 6);

        assert!(mex.remove(&0));
        assert_eq!(mex.len(), 5);
        assert_eq!(mex.minimum_excluded(), 0);
    }

    #[test]
    fn test_iterators() {
        // Test FromIterator
        let mex: MexSet<u32> = MexSet::from_iter(
            vec![5, 1, 4, 2, 3].into_iter()
        );
        assert_eq!(mex.len(), 5);
        assert_eq!(
            mex.into_iter().collect::<HashSet<u32>>(), 
            HashSet::from_iter(vec![5, 1, 4, 2, 3].into_iter()),
        );

        let mex: MexSet<u32> = vec![5, 1, 4, 2, 3].into_iter().collect();
        assert_eq!(mex.len(), 5);
        assert_eq!(
            mex.into_iter().collect::<HashSet<u32>>(),
            HashSet::from_iter(vec![5, 1, 4, 2, 3].into_iter()),
        );

        let mex: MexSet<u32> = MexSet::from_iter(
            vec![5, 1, 4, 2, 3].into_iter()
        );

        println!("{:?}", mex);

        assert_eq!(
            mex.iter().collect::<HashSet<&u32>>(),
            vec![&1, &2, &3, &4, &5].into_iter().collect::<HashSet<&u32>>(),
        );

        assert_eq!(
            mex.into_iter().collect::<HashSet<u32>>(),
            vec![1, 2, 3, 4, 5].into_iter().collect::<HashSet<u32>>(),
        );
    }

    #[test]
    fn test_clone_eq() {
        let mex: MexSet<u32> = MexSet::from_iter(
            vec![5, 1, 4, 2, 3].into_iter()
        );

        let mut cmex = mex.clone();        
        assert_eq!(mex, cmex);

        cmex.remove(&2);
        assert_ne!(mex, cmex);
    }

    #[test]
    fn test_with_range() {
        let mex: MexSet<u32> = MexSet::from_iter(
            vec![5, 1, 4, 2, 0, 3].into_iter()
        );

        assert_eq!(
            MexSet::with_range(6u32),
            mex,
        )
    }
}
