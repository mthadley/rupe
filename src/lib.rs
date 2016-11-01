extern crate core;
extern crate unicode_segmentation;

use core::iter::FlatMap;
use std::cmp::max;
use unicode_segmentation::{Graphemes as USGraphemes, UnicodeSegmentation};

#[derive(Clone)]
pub enum Rope {
    Node(usize, Box<Rope>, Box<Rope>),
    Leaf(String),
}

use self::Rope::{Node, Leaf};

type Graphemes<'a> = FlatMap<Strings<'a>, USGraphemes<'a>, fn(&str) -> USGraphemes>;

impl Rope {
    /// Creates a new `Rope`.
    pub fn new<T: Into<String>>(val: T) -> Self {
        Leaf(val.into())
    }

    /// Returns a String representing the contents of a `Rope`.
    pub fn to_string(&self) -> String {
        self.strings().collect()
    }

    /// Returns an `Iterator` over the Grapheme clusters of a `Rope`.
    pub fn graphemes<'a>(&'a self) -> Graphemes<'a> {
        self.strings().flat_map(Self::map_graphemes)
    }

    fn map_graphemes(string: &str) -> USGraphemes {
        string.graphemes(true)
    }

    /// Returns an `Iterator` over the lines of a `Rope`.
    pub fn lines(&self) -> Lines {
        Lines { graphemes: self.graphemes() }
    }

    /// Concatenates two ropes together and returns a new `Rope`.
    pub fn concat<T: Into<Rope>>(self, val: T) -> Rope {
        let rope: Rope = val.into();
        let self_len = self.length();

        if self_len == 0 {
            rope
        } else if rope.length() == 0 {
            self
        } else {
            Node(self_len, Box::from(self), Box::from(rope))
        }
    }

    /// Returns the depth of the underlying tree representing the `Rope`.
    pub fn height(&self) -> usize {
        match *self {
            Node(_, ref left, ref right) => 1 + max(left.height(), right.height()),
            _ => 1,
        }
    }

    /// Inserts `T` at `i` into the rope, consuming the current `Rope`.
    pub fn insert<T: Into<Rope>>(self, val: T, i: usize) -> Rope {
        let (left, right) = self.split(i);
        left.concat(val).concat(right)
    }

    /// Returns the `length` of the rope. In this case the length is number of grapheme clusters
    /// and not the number of `bytes` like a normal `String`.
    pub fn length(&self) -> usize {
        match *self {
            Node(s, _, ref right) => s + right.length(),
            Leaf(ref string) => string.graphemes(true).count(),
        }
    }

    /// Removes the grapheme at `i`, consuming the `Rope`.
    pub fn remove_at(self, i: usize) -> Rope {
        self.remove_range(i, i + 1)
    }

    /// Removes a range from the `Rope`, consuming it.
    pub fn remove_range(self, i: usize, j: usize) -> Rope {
        assert!(j >= i, "Range end should not be less than it's start.");
        let (left, temp) = self.split(i);
        let (_, right) = temp.split(j - i);
        left.concat(right)
    }

    /// Splits the `Rope` at `i`, returning tuple of `Rope`s representing the left and right
    /// branches:
    ///
    /// ```rust
    /// use rupe::Rope;
    ///
    /// let rope = Rope::new("foobar");
    /// let (left, right) = rope.clone().split(3);
    /// assert_eq!(left.to_string(), "foo");
    /// assert_eq!(right.to_string(), "bar");
    /// ```
    pub fn split(self, i: usize) -> (Rope, Rope) {
        match self {
            Node(s, left, right) => {
                if i < s {
                    let (a, b) = left.split(i);
                    (a, b.concat(*right))
                } else if i > s {
                    let (a, b) = right.split(i - s);
                    (left.concat(a), b)
                } else {
                    (*left, *right)
                }
            }
            Leaf(string) => {
                let mut left = String::new();
                let mut right = String::new();

                for (j, s) in string.graphemes(true).enumerate() {
                    if j < i {
                        left.push_str(s)
                    } else {
                        right.push_str(s)
                    }
                }

                (left.into(), right.into())
            }
        }
    }

    pub fn strings(&self) -> Strings {
        Strings::new(self)
    }
}

/// An `Iterator` over the lines of a `Rope`.
pub struct Lines<'a> {
    graphemes: Graphemes<'a>,
}

impl<'a> Iterator for Lines<'a> {
    type Item = String;

    fn next(&mut self) -> Option<Self::Item> {
        let mut line = String::new();

        while let Some(ref gh) = self.graphemes.next() {
            match gh {
                &"\n" => return Some(line),
                _ => line.push_str(gh),
            }
        }

        if line.len() > 0 { Some(line) } else { None }
    }
}

/// An `Iterator` over the `String`s of a `Rope`.
pub struct Strings<'a> {
    stack: Vec<&'a Rope>,
    current: Option<&'a str>,
}

impl<'a> Strings<'a> {
    pub fn new(node: &Rope) -> Strings {
        let mut iter = Strings {
            stack: Vec::new(),
            current: None,
        };
        iter.load_stack(node);
        iter
    }

    fn load_stack(&mut self, mut node: &'a Rope) {
        loop {
            match node {
                &Node(_, ref left, ref right) => {
                    self.stack.push(right);
                    node = left;
                }
                &Leaf(ref string) => {
                    self.current = Some(string);
                    break;
                }
            }
        }
    }
}

impl<'a> Iterator for Strings<'a> {
    type Item = &'a str;

    fn next(&mut self) -> Option<Self::Item> {
        let result = self.current.take();
        if let Some(node) = self.stack.pop() {
            self.load_stack(node);
        }
        result
    }
}

impl From<Rope> for String {
    fn from(rope: Rope) -> Self {
        rope.to_string()
    }
}

impl From<String> for Rope {
    fn from(string: String) -> Self {
        Rope::new(string)
    }
}

impl From<&'static str> for Rope {
    fn from(string: &'static str) -> Self {
        Rope::new(String::from(string))
    }
}

#[cfg(test)]
mod test {
    use super::*;

    fn node<T: Into<Rope>, U: Into<Rope>>(size: usize, left: T, right: U) -> Rope {
        Rope::Node(size, Box::from(left.into()), Box::from(right.into()))
    }

    fn leaf<T: Into<String>>(val: T) -> Rope {
         Rope::Leaf(val.into())
    }

    fn create_rope() -> Rope {
        node(6,
             node(3, "foo", "bar"),
             node(3, "baz", node(4, "fizz", "buzz")))
    }

    #[test]
    fn new() {
        let rope = Rope::new("test");

        assert_eq!(rope.to_string(), "test");
        assert_eq!(rope.length(), 4);
    }

    #[test]
    fn to_string() {
       let rope = node(4, "test", " string");

       assert_eq!(rope.to_string(), "test string");
   }

   #[test]
   fn height() {
       let left = leaf("foo");
       assert_eq!(left.height(), 1);

       let right = node(3, "bar", "baz");
       assert_eq!(right.height(), 2);

        let rope = node(3, left, right);
        assert_eq!(rope.height(), 3);
    }

    #[test]
    fn length() {
        let left = leaf("foo");
        assert_eq!(left.length(), 3);

        let right = node(3, "bar", "baz");
        assert_eq!(right.length(), 6);

        let rope = node(3, left, right);
        assert_eq!(rope.length(), 9);

        assert_eq!(node(5, "a̐éö̲\r\n", "éö̲\r").length(), 8);
        assert_eq!(Rope::new("a̐éö̲\r\n").length(), 4);
    }

    #[test]
    fn concat() {
        let second = node(3, "baz", "biz");
        let third = node(4, "fizz", "buzz");

        let mut rope = Rope::new("foo").concat("bar");
        assert_eq!(rope.height(), 2);
        assert_eq!(rope.length(), 6);
        assert_eq!(rope.to_string(), "foobar");

        rope = rope.concat(second);
        assert_eq!(rope.height(), 3);
        assert_eq!(rope.length(), 12);
        assert_eq!(rope.to_string(), "foobarbazbiz");

        rope = rope.concat(third);
        assert_eq!(rope.height(), 4);
        assert_eq!(rope.length(), 20);
        assert_eq!(rope.to_string(), "foobarbazbizfizzbuzz");
    }

    #[test]
    fn strings() {
        let mut rope = node(3, "foo", "bar");

        {
            let strings = rope.strings().collect::<Vec<_>>();
            assert_eq!(strings, vec!["foo", "bar"]);
        }

        rope = node(6, node(3, "foo", "bar"), "baz");
        assert_eq!(9, rope.length());

        {
            let strings = rope.strings().collect::<Vec<_>>();
            assert_eq!(strings, vec!["foo", "bar", "baz"]);
        }

        rope = rope.concat("biz");
        assert_eq!(12, rope.length());
        let strings = rope.strings().collect::<Vec<_>>();
        assert_eq!(strings, vec!["foo", "bar", "baz", "biz"]);
    }

    #[test]
    fn graphemes() {
        let rope = create_rope();
        let graphemes: Vec<_> = rope.graphemes().collect();
        let expected: Vec<_> = "foobarbazfizzbuzz".chars().map(|c| c.to_string()).collect();
        assert_eq!(graphemes, expected);

        let rope = node(5, "a̐éö̲\r\n", "éö̲\r");
        let graphemes: Vec<_> = rope.graphemes().collect();
        let expected = vec!["a̐", "é", "ö̲", "\r\n", "é", "ö̲", "\r"];
        assert_eq!(graphemes, expected);
    }

    #[test]
    fn split() {
        let rope = node(3, "foo", "bar");

        let (left, right) = rope.clone().split(3);
        assert_eq!(left.to_string(), "foo");
        assert_eq!(right.to_string(), "bar");

        let (left, right) = rope.clone().split(0);
        assert_eq!(left.to_string(), "");
        assert_eq!(right.to_string(), "foobar");

        let (left, right) = rope.clone().split(6);
        assert_eq!(left.to_string(), "foobar");
        assert_eq!(right.to_string(), "");

        let (left, right) = create_rope().clone().split(9);
        assert_eq!(left.to_string(), "foobarbaz");
        assert_eq!(right.to_string(), "fizzbuzz");

        let (left, right) = create_rope().clone().split(15);
        assert_eq!(left.to_string(), "foobarbazfizzbu");
        assert_eq!(left.length(), 15);
        assert_eq!(right.to_string(), "zz");

        let (left, right) = create_rope().clone().split(2);
        assert_eq!(left.to_string(), "fo");
        assert_eq!(left.length(), 2);
        assert_eq!(right.to_string(), "obarbazfizzbuzz");

    }

    #[test]
    fn insert() {
        let rope = create_rope().insert("test", 3);
        assert_eq!(rope.to_string(), "footestbarbazfizzbuzz");

        let rope = create_rope().insert("test", 9);
        assert_eq!(rope.to_string(), "foobarbaztestfizzbuzz");

        let rope = create_rope().insert("test", 0);
        assert_eq!(rope.to_string(), "testfoobarbazfizzbuzz");

        let rope = create_rope().insert("test", 50);
        assert_eq!(rope.to_string(), "foobarbazfizzbuzztest");
    }

    #[test]
    fn remove_range() {
        let rope = create_rope().remove_range(3, 6);
        assert_eq!(rope.to_string(), "foobazfizzbuzz");

        let rope = Rope::new("abc").remove_range(2, 6);
        assert_eq!(rope.to_string(), "ab");
    }

    #[test]
    #[should_panic(expected = "Range end should not be less than it's start.")]
    fn remove_range_should_panic() {
        create_rope().remove_range(4, 2);
    }

    #[test]
    fn remove_at() {
        let rope = Rope::new("abc").remove_at(1);
        assert_eq!(rope.to_string(), "ac");

        let rope = Rope::new("abc").remove_at(6);
        assert_eq!(rope.to_string(), "abc");
    }

    #[test]
    fn lines() {
        let rope = Rope::new("abc\ndef\nghi");
        assert_eq!(rope.lines().collect::<Vec<_>>(), vec!["abc", "def", "ghi"]);
    }
}
