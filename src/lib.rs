//! https://jasonkayzk.github.io/2022/02/20/使用Rust实现一个双向链表/

use std::{error::Error, fmt::Debug, marker::PhantomData, mem, ptr::NonNull};

#[derive(Debug, Clone)]
pub struct IndexOutOfRangeError;

impl std::fmt::Display for IndexOutOfRangeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "index out of range")
    }
}

impl std::error::Error for IndexOutOfRangeError {}

pub struct IntoIter<T> {
    list: LinkedList<T>,
}

impl<T> Iterator for IntoIter<T> {
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.list.pop_front()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.list.length, Some(self.list.length))
    }
}

impl<T> DoubleEndedIterator for IntoIter<T> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.list.pop_back()
    }
}

impl<T> Drop for IntoIter<T> {
    fn drop(&mut self) {
        for _ in &mut *self {}

        println!("IntoIter has been dropped!");
    }
}

pub struct Iter<'a, T: 'a> {
    head: Option<NonNull<Node<T>>>,
    tail: Option<NonNull<Node<T>>>,
    len: usize,
    _marker: PhantomData<&'a Node<T>>,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.len == 0 {
            None
        } else {
            self.head.map(|node| {
                self.len -= 1;
                unsafe {
                    let node = &*node.as_ptr();
                    self.head = node.next;
                    &node.val
                }
            })
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }

    #[inline]
    fn last(mut self) -> Option<&'a T> {
        self.next_back()
    }
}

impl<'a, T> DoubleEndedIterator for Iter<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.len == 0 {
            None
        } else {
            self.tail.map(|node| {
                self.len -= 1;
                unsafe {
                    let node = &*node.as_ptr();
                    self.tail = node.prev;
                    &node.val
                }
            })
        }
    }
}

impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = &'a mut T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.len == 0 {
            None
        } else {
            self.head.map(|node| {
                self.len -= 1;
                unsafe {
                    let node = &mut *(node.as_ptr());
                    self.head = node.next;
                    &mut node.val
                }
            })
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }

    #[inline]
    fn last(mut self) -> Option<&'a mut T> {
        self.next_back()
    }
}

impl<'a, T> DoubleEndedIterator for IterMut<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.len == 0 {
            None
        } else {
            self.tail.map(|node| {
                self.len -= 1;
                unsafe {
                    let node = &mut *(node.as_ptr());
                    self.tail = node.prev;
                    &mut node.val
                }
            })
        }
    }
}

pub struct IterMut<'a, T: 'a> {
    head: Option<NonNull<Node<T>>>,
    tail: Option<NonNull<Node<T>>>,
    len: usize,
    _marker: PhantomData<&'a mut Node<T>>,
}

struct Node<T> {
    val: T,
    next: Option<NonNull<Node<T>>>,
    prev: Option<NonNull<Node<T>>>,
}

impl<T> Node<T> {
    fn new(val: T) -> Node<T> {
        Node {
            val,
            prev: None,
            next: None,
        }
    }

    fn into_val(self) -> T {
        self.val
    }
}

pub struct LinkedList<T> {
    length: usize,
    head: Option<NonNull<Node<T>>>,
    tail: Option<NonNull<Node<T>>>,
    _marker: PhantomData<Box<Node<T>>>,
}

impl<T> Default for LinkedList<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> LinkedList<T> {
    pub fn new() -> Self {
        Self {
            length: 0,
            head: None,
            tail: None,
            _marker: PhantomData,
        }
    }

    pub fn push_front(&mut self, val: T) {
        // 包装元素
        let mut node = Box::new(Node::new(val));
        // 在链表的最前端插入node
        // node 的 next 节点为当前链表的头节点
        // node 的 prev 节点为None
        node.next = self.head;
        node.prev = None;
        let node = NonNull::new(Box::into_raw(node));

        match self.head {
            None => self.tail = node,
            Some(head) => unsafe { (*head.as_ptr()).prev = node },
        }
        self.head = node;
        self.length += 1;
    }

    pub fn push_back(&mut self, val: T) {
        let mut node = Box::new(Node::new(val));
        node.next = None;
        node.prev = self.tail;
        let node = NonNull::new(Box::into_raw(node));

        match self.tail {
            None => self.head = node,
            Some(tail) => unsafe {
                (*tail.as_ptr()).next = node;
            },
        }

        self.tail = node;
        self.length += 1;
    }

    pub fn pop_front(&mut self) -> Option<T> {
        // 使用 map 处理 head
        self.head.map(|node| {
            self.length -= 1;

            unsafe {
                // 获取头节点，并将下一个节点设置为头节点
                let node = Box::from_raw(node.as_ptr());
                self.head = node.next;

                match self.head {
                    None => self.tail = None, // 如果新的头节点为None，则tail也是None
                    Some(head) => (*head.as_ptr()).prev = None, // 将新的头节点的前节点设置为None
                }
                node.into_val()
            }
        })
    }

    pub fn pop_back(&mut self) -> Option<T> {
        self.tail.map(|node| {
            self.length -= 1;

            unsafe {
                let node = Box::from_raw(node.as_ptr());
                self.tail = node.prev;

                match self.tail {
                    None => self.head = None,
                    Some(tail) => (*tail.as_ptr()).next = None,
                }
                node.into_val()
            }
        })
    }

    pub fn peek_front(&self) -> Option<&T> {
        unsafe { self.head.as_ref().map(|node| &node.as_ref().val) }
    }

    pub fn peek_front_mut(&mut self) -> Option<&mut T> {
        unsafe { self.head.as_mut().map(|node| &mut node.as_mut().val) }
    }

    pub fn peek_back(&self) -> Option<&T> {
        unsafe { self.tail.as_ref().map(|node| &node.as_ref().val) }
    }

    pub fn peek_back_mut(&mut self) -> Option<&mut T> {
        unsafe { self.tail.as_mut().map(|node| &mut node.as_mut().val) }
    }

    fn _get_by_idx_mut(&self, idx: usize) -> Result<Option<NonNull<Node<T>>>, Box<dyn Error>> {
        let len = self.length;
        if idx >= len {
            return Err(Box::new(IndexOutOfRangeError));
        }

        let offset_from_end = len - idx - 1;
        let mut cur;
        // 如果idx大于offset_from_end说明idx位于前半部分，从head开始查找
        // 因为 NonNull 实现了Copy、Clone trait，所以 cur.take() 消耗的是cur本身
        if idx <= offset_from_end {
            cur = self.head;
            for _ in 0..idx {
                match cur.take() {
                    None => cur = self.head,
                    Some(current) => unsafe {
                        cur = current.as_ref().next;
                    },
                }
            }
        } else {
            // 由尾部往上找
            cur = self.tail;
            for _ in 0..offset_from_end {
                match cur.take() {
                    None => cur = self.tail,
                    Some(current) => unsafe {
                        cur = current.as_ref().prev;
                    },
                }
            }
        }
        Ok(cur)
    }

    pub fn get_by_idx(&self, idx: usize) -> Result<Option<&T>, Box<dyn Error>> {
        let cur = self._get_by_idx_mut(idx)?;
        unsafe { Ok(cur.as_ref().map(|node| &node.as_ref().val)) }
    }

    pub fn get_by_idx_mut(&self, idx: usize) -> Result<Option<&mut T>, Box<dyn Error>> {
        let mut cur = self._get_by_idx_mut(idx)?;
        unsafe { Ok(cur.as_mut().map(|node| &mut node.as_mut().val)) }
    }

    pub fn insert_by_idx(&mut self, idx: usize, data: T) -> Result<(), Box<dyn Error>> {
        let len = self.length;

        if idx > len {
            return Err(Box::new(IndexOutOfRangeError {}));
        }

        if idx == 0 {
            return {
                self.push_front(data);
                Ok(())
            };
        } else if idx == len {
            return {
                self.push_back(data);
                Ok(())
            };
        }

        unsafe {
            // Create Node
            let mut spliced_node = Box::new(Node::new(data));
            let before_node = self._get_by_idx_mut(idx - 1)?;
            let after_node = before_node.unwrap().as_mut().next;
            spliced_node.prev = before_node;
            spliced_node.next = after_node;
            let spliced_node = NonNull::new(Box::into_raw(spliced_node));

            // Insert Node
            before_node.unwrap().as_mut().next = spliced_node;
            after_node.unwrap().as_mut().prev = spliced_node;
        }

        self.length += 1;

        Ok(())
    }

    pub fn remove_by_idx(&mut self, idx: usize) -> Result<T, Box<dyn Error>> {
        let len = self.length;
        if idx >= len {
            return Err(Box::new(IndexOutOfRangeError));
        }
        if idx == 0 {
            return Ok(self.pop_front().unwrap());
        } else if idx == len - 1 {
            return Ok(self.pop_back().unwrap());
        }
        let cur = self._get_by_idx_mut(idx)?.unwrap();
        self.unlink_node(cur);

        unsafe {
            let unlinked_node = Box::from_raw(cur.as_ptr());
            Ok(unlinked_node.val)
        }
    }

    fn unlink_node(&mut self, mut node: NonNull<Node<T>>) {
        let node = unsafe { node.as_mut() };

        // 如果当前节点的 prev 节点有值，则将上一个节点的 next 指向当前节点的 next
        // 如果当前节点的 prev 节点没有值，则说明当前节点为链表的头节点，则将链表的头节点指向当前节点的 next
        match node.prev {
            Some(prev) => unsafe { (*prev.as_ptr()).next = node.next },
            None => self.head = node.next,
        }

        // 如果当前节点的下一个节点有值，则将下一个节点的 prev 指向当前节点的上一个节点
        // 如果当前节点的下一个节点没有值，则说明当前节点为链表的尾节点，则将链表的尾节点指向当前节点的上一个节点
        match node.next {
            Some(next) => unsafe { (*next.as_ptr()).prev = node.prev },
            None => self.tail = node.prev,
        }

        self.length -= 1;
    }

    #[allow(clippy::should_implement_trait)]
    pub fn into_iter(self) -> IntoIter<T> {
        IntoIter { list: self }
    }

    pub fn iter(&self) -> Iter<'_, T> {
        Iter {
            head: self.head,
            tail: self.tail,
            len: self.length,
            _marker: PhantomData,
        }
    }

    pub fn iter_mut(&mut self) -> IterMut<'_, T> {
        IterMut {
            head: self.head,
            tail: self.tail,
            len: self.length,
            _marker: PhantomData,
        }
    }

    pub fn contains(&self, elem: &T) -> bool
    where
        T: PartialEq<T>,
    {
        self.iter().any(|x| x == elem)
    }

    pub fn clear(&mut self) {
        *self = Self::new();
    }
}

impl<T: Debug> LinkedList<T>
where
    T: Debug,
{
    pub fn traverse(&self) {
        print!("{{ ");
        for (idx, x) in self.iter().enumerate() {
            print!(" [{}: {:?}] ", idx, *x);
        }
        print!(" }}");
    }
}

impl<T> Drop for LinkedList<T> {
    fn drop(&mut self) {
        struct DropGuard<'a, T>(&'a mut LinkedList<T>);

        impl<'a, T> Drop for DropGuard<'a, T> {
            fn drop(&mut self) {
                while self.0.pop_front().is_some() {}
            }
        }

        while let Some(node) = self.pop_front() {
            let guard = DropGuard(self);
            drop(node);
            mem::forget(guard);
        }
        // println!("LinkedList dropped!");
    }
}

#[cfg(test)]
mod test {
    use crate::LinkedList;

    #[test]
    fn test_compiling() {}

    #[test]
    fn test_push_and_pop() {
        let mut list = _new_list_i32();

        assert_eq!(list.length, 5);
        list.traverse();

        assert_eq!(list.pop_front(), Some(-1));
        assert_eq!(list.pop_back(), Some(i32::MAX));

        assert_eq!(list.length, 3);
        list.traverse();
    }

    #[test]
    fn test_peak() {
        let mut list = _new_list_string();

        assert_eq!(list.peek_front(), Some(&String::from("abc")));
        assert_eq!(list.peek_back(), Some(&String::from("hij")));

        let cur = list.peek_front_mut();
        assert_eq!(cur, Some(&mut String::from("abc")));
        cur.map(|x| x.push(' '));

        let cur = list.peek_back_mut();
        assert_eq!(cur, Some(&mut String::from("hij")));
        cur.map(|x| x.push(' '));

        assert_eq!(list.peek_front(), Some(&String::from("abc ")));
        assert_eq!(list.peek_back(), Some(&String::from("hij ")));
        assert_eq!(list.length, 3);

        list.traverse();
    }

    #[test]
    fn test_get_idx() {
        let list = _new_list_i32();

        assert_eq!(list.get_by_idx(2).unwrap(), Some(&456));
        assert_eq!(list.get_by_idx(3).unwrap(), Some(&789));

        print!("before change: ");
        list.traverse();
        let cur = list.get_by_idx_mut(2).unwrap().unwrap();
        assert_eq!(cur, &mut 456);

        *cur <<= 1;
        print!("after change: ");
        list.traverse();

        assert_eq!(list.get_by_idx(2).unwrap(), Some(&(456 << 1)));
    }

    #[test]
    fn test_get_idx_err() {
        let list = _new_list_i32();

        assert!(list.get_by_idx(99).is_err());
        assert!(list.get_by_idx_mut(99).is_err());
    }

    #[test]
    fn test_insert_idx() {
        let mut list = LinkedList::new();

        list.push_back(String::from("1"));
        list.push_back(String::from("2"));
        list.push_back(String::from("3"));

        list.insert_by_idx(1, String::from("99")).unwrap();
        list.traverse();

        assert_eq!(list.get_by_idx(0).unwrap(), Some(&String::from("1")));
        assert_eq!(list.get_by_idx(1).unwrap(), Some(&String::from("99")));
    }

    #[test]
    fn test_insert_idx_err() {
        let mut list = LinkedList::new();

        assert!(list.insert_by_idx(99, String::from("99")).is_err());
    }

    #[test]
    fn test_remove_idx() {
        let mut list = LinkedList::new();

        list.push_back(String::from("1"));
        list.push_back(String::from("2"));
        list.push_back(String::from("3"));

        let removed = list.remove_by_idx(1).unwrap();
        list.traverse();

        assert_eq!(removed, String::from("2"));

        assert_eq!(list.get_by_idx(0).unwrap(), Some(&String::from("1")));
        assert_eq!(list.get_by_idx(1).unwrap(), Some(&String::from("3")));
    }

    #[test]
    fn test_remove_idx_err() {
        let mut list: LinkedList<i32> = LinkedList::new();

        assert!(list.remove_by_idx(99).is_err());
    }

    #[test]
    fn test_contains() {
        let list = _new_list_i32();

        assert!(list.contains(&-1));
        assert!(!list.contains(&-2));
    }

    #[test]
    fn test_clear() {
        let mut list = _new_list_zst();

        assert_eq!(list.length, 3);

        list.clear();

        assert_eq!(list.length, 0);
    }

    #[test]
    fn test_iterator() {
        let mut list1 = _new_list_i32();

        print!("before change: ");
        list1.traverse();
        list1.iter_mut().for_each(|x| *x = *x - 1);
        print!("after change: ");
        list1.traverse();

        let list2 = _new_list_string();
        let list2_to_len = list2.into_iter().map(|x| x.len()).collect::<Vec<usize>>();
        println!(
            "transform list2 into len vec, list2_to_len: {:?}",
            list2_to_len
        );
    }

    struct ZeroSizeType {}

    fn _new_list_i32() -> LinkedList<i32> {
        let mut list = LinkedList::new();

        list.push_front(456);
        list.push_front(123);
        list.push_back(789);
        list.push_front(-1);
        list.push_back(i32::MAX);

        list
    }

    fn _new_list_string() -> LinkedList<String> {
        let mut list = LinkedList::new();

        list.push_front(String::from("def"));
        list.push_front(String::from("abc"));
        list.push_back(String::from("hij"));

        list
    }

    fn _new_list_zst() -> LinkedList<ZeroSizeType> {
        let mut list = LinkedList::new();

        list.push_front(ZeroSizeType {});
        list.push_front(ZeroSizeType {});
        list.push_back(ZeroSizeType {});

        list
    }
}
