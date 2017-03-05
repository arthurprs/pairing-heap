#![feature(test)]

#[cfg(test)]
extern crate test;
#[cfg(test)]
extern crate rand;
extern crate stash;

#[derive(Debug, PartialEq, Eq, Copy, Clone)]
struct Handle(u32);

#[derive(Clone)]
struct Node<T> {
    prev: Handle,
    next: Handle,
    child: Handle,
    value: T,
}

#[derive(Clone)]
struct Heap<T> {
    root: Handle,
    nodes: stash::Stash<Node<T>, Handle>,
}

const NULL: Handle = Handle(0xFFFFFFFF);

impl<T: PartialOrd> Heap<T> {
    pub fn new() -> Self {
        Heap {
            root: NULL,
            nodes: Default::default(),
        }
    }

    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn clear(&mut self) {
        self.root = NULL;
        self.nodes.clear();
    }

    pub fn peek(&self) -> Option<&T> {
        self.nodes.get(self.root).map(|n| &n.value)
    }

    pub fn push(&mut self, value: T) -> Handle {
        let inserted = self.nodes.put(Node::with(value));
        let old_root = self.root;
        if old_root == NULL {
            self.root = inserted;
        } else {
            // faster version of merge, that asssumes
            // root/inserted.prev/next == NULL
            // inserted,child == NULL
            debug_assert!(self.node_mut(inserted).child == NULL);
            debug_assert!(self.node_mut(inserted).prev == NULL);
            debug_assert!(self.node_mut(inserted).next == NULL);
            debug_assert!(self.node_mut(old_root).prev == NULL);
            debug_assert!(self.node_mut(old_root).next == NULL);
            let (p, c, p_c) = if self.node(old_root).value > self.node(inserted).value {
                let p_c = ::std::mem::replace(&mut self.node_mut(old_root).child, inserted);
                if p_c != NULL {
                    self.node_mut(p_c).prev = inserted;
                }
                (old_root, inserted, p_c)
            } else {
                self.node_mut(inserted).child = old_root;
                self.root = inserted;
                (inserted, old_root, NULL)
            };

            let child = self.node_mut(c);
            child.next = p_c;
            child.prev = p;            
        }
        inserted
    }

    pub fn pop(&mut self) -> Option<T> {
        let old_root = self.root;
        self.remove(old_root)
    }

    pub fn remove(&mut self, handle: Handle) -> Option<T> {
        if let Some(node) = self.nodes.take(handle) {
            if handle == self.root {
                debug_assert!(node.prev == NULL);
                debug_assert!(node.next == NULL);
                self.root = self.colapse_nodes(node.child);
            } else {
                if node.prev != NULL {
                    let prev_node = self.node_mut(node.prev);
                    if prev_node.child == handle {
                        prev_node.child = node.next;
                    } else {
                        prev_node.next = node.next;
                    }
                }

                if node.next != NULL {
                    self.node_mut(node.next).prev = node.prev;
                }

                let child = self.colapse_nodes(node.child);
                let old_root = self.root;
                self.root = self.merge_nodes(old_root, child);
            }
            Some(node.value)
        } else {
            None
        }
    }

    fn increase_key(&mut self, handle: Handle, value: T) {
        if handle == self.root {
            self.node_mut(handle).value = value;
            return;
        }

        let (prev, next) = {
            let node = self.node_mut(handle);
            assert!(value >= node.value);
            node.value = value;
            (node.prev, node.next)
        };
        if prev != NULL {
            let prev_node = self.node_mut(prev);
            if prev_node.child == handle {
                prev_node.child = next;
            } else {
                prev_node.next = next;
            }
        }
        if next != NULL {
            self.node_mut(next).prev = prev;
        }

        let old_root = self.root;
        self.root = self.merge_nodes(old_root, handle);
    }

    fn merge_nodes(&mut self, a: Handle, b: Handle) -> Handle {
        if a == NULL {
            b
        } else if b == NULL {
            a
        } else {
            debug_assert!(a != b);
            let (p, c) = if self.node(a).value > self.node(b).value {
                (a, b)
            } else {
                (b, a)
            };
            let p_c = {
                let parent = self.node_mut(p);
                parent.next = NULL;
                parent.prev = NULL;
                ::std::mem::replace(&mut parent.child, c)
            };
            if p_c != NULL {
                self.node_mut(p_c).prev = c;
            }
            {
                let child = self.node_mut(c);
                child.next = p_c;
                child.prev = p;
            }
            p
        }
    }
    
    fn colapse_nodes(&mut self, handle: Handle) -> Handle {
        if handle == NULL {
            return NULL;
        }

        let mut next = handle;
        let mut tail = NULL;
        let mut result = NULL;
        while next != NULL {
            let a = next;
            let b = self.node(a).next;
            if b != NULL {
                next = self.node(b).next;
                result = self.merge_nodes(a, b);
                // track the result onto the end of the temporary list
                self.node_mut(result).prev = tail;
                tail = result;
            } else {
                self.node_mut(a).prev = tail;
                tail = a;
                break;
            }
        }

        result = NULL;
        while tail != NULL {
            // trace back through to merge the list
            next = self.node(tail).prev;
            result = self.merge_nodes(result, tail);
            tail = next;
        }

        result
    }

    #[inline]
    fn node(&self, h: Handle) -> &Node<T> {
        if cfg!(debug_assertions) {
            self.nodes.get(h).unwrap_or_else(||
                panic!("{:?} isn't a valid handle", h)
            )
        } else {
            unsafe { self.nodes.get_unchecked(h) }
        }
    }

    #[inline]
    fn node_mut(&mut self, h: Handle) -> &mut Node<T> {
        if cfg!(debug_assertions) {
            self.nodes.get_mut(h).unwrap_or_else(||
                panic!("{:?} isn't a valid handle", h)
            )
        } else {
            unsafe { self.nodes.get_unchecked_mut(h) }
        }
    }
}

impl<T> Node<T> {
    fn with(value: T) -> Self {
        Node {
            value: value,
            prev: NULL,
            next: NULL,
            child: NULL,
        }
    }
}

impl<T: PartialOrd, I: IntoIterator<Item=T>> From<I> for Heap<T> {
    fn from(from: I) -> Self {
        let mut heap = Self::new();
        for v in from {
            heap.push(v);
        }
        heap
    }
}

impl stash::Index for Handle {
    fn from_usize(u: usize) -> Self {
        Handle(u as _)
    }
    fn into_usize(self) -> usize {
        self.0 as _
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_remove() {
        let data = vec![2, 4, 6, 2, 1, 8, 10, 3, 5, 7, 0, 9, 1];
        let mut sorted = data.clone();
        sorted.sort();
        let mut heap = Heap::from(data);

        let a = heap.push(1000);
        let b = heap.push(-1000);
        let c = heap.push(5);
        println!("a:{:?} b:{:?}", a, b);
        assert_eq!(heap.remove(a).unwrap(), 1000);
        assert_eq!(heap.remove(b).unwrap(), -1000);
        assert_eq!(heap.remove(c).unwrap(), 5);

        while !heap.is_empty() {
            assert_eq!(heap.peek().unwrap(), sorted.last().unwrap());
            assert_eq!(heap.pop().unwrap(), sorted.pop().unwrap());
        }
    }
    
    #[test]
    fn test_increase_key() {
        let mut heap = Heap::new();
        let a = heap.push(1);
        let b = heap.push(2);
        let c = heap.push(3);
        assert_eq!(*heap.peek().unwrap(), 3);
        heap.increase_key(a, 3);
        assert_eq!(*heap.peek().unwrap(), 3);
        heap.increase_key(a, 4);
        assert_eq!(*heap.peek().unwrap(), 4);
        heap.increase_key(a, 5);
        assert_eq!(heap.pop().unwrap(), 5);
        assert_eq!(heap.pop().unwrap(), 3);
        assert_eq!(heap.pop().unwrap(), 2);
    }

    #[test]
    fn test_push() {
        let mut heap = Heap::from(vec![2, 4, 9]);
        assert_eq!(heap.len(), 3);
        assert!(*heap.peek().unwrap() == 9);
        heap.push(11);
        assert_eq!(heap.len(), 4);
        assert!(*heap.peek().unwrap() == 11);
        heap.push(5);
        assert_eq!(heap.len(), 5);
        assert!(*heap.peek().unwrap() == 11);
        heap.push(27);
        assert_eq!(heap.len(), 6);
        assert!(*heap.peek().unwrap() == 27);
        heap.push(3);
        assert_eq!(heap.len(), 7);
        assert!(*heap.peek().unwrap() == 27);
        heap.push(103);
        assert_eq!(heap.len(), 8);
        assert!(*heap.peek().unwrap() == 103);
    }

    #[test]
    fn test_peek_and_pop() {
        let data = vec![2, 4, 6, 2, 1, 8, 10, 3, 5, 7, 0, 9, 1];
        let mut sorted = data.clone();
        sorted.sort();
        let mut heap = Heap::from(data);
        while !heap.is_empty() {
            assert_eq!(heap.peek().unwrap(), sorted.last().unwrap());
            assert_eq!(heap.pop().unwrap(), sorted.pop().unwrap());
        }
    }

    #[test]
    fn test_empty_pop() {
        let mut heap = Heap::<i32>::new();
        assert!(heap.pop().is_none());
    }

    #[test]
    fn test_empty_peek() {
        let empty = Heap::<i32>::new();
        assert!(empty.peek().is_none());
    }
}

#[cfg(test)]
mod bench {
    use test::{Bencher, black_box};
    use super::Heap as PairingHeap;
    use ::std::collections::BinaryHeap;

	fn setup_sample() -> Vec<(i64, i64)> {
		use rand::{thread_rng, sample};
		let n       = 1000;
		let mut rng = thread_rng();
		sample(&mut rng, (0..n).map(|x| (-x, -x)), n as usize)
        // (0..n).map(|x| (-x, -x)).collect()
    }
    
	#[bench]
	fn pairing_heap_push(bencher: &mut Bencher) {
		let sample = setup_sample();
		bencher.iter(|| {
			let mut ph = PairingHeap::new();
			for &key in sample.iter() {
				black_box(ph.push(key));
			}
		});
	}


	#[bench]
	fn binary_heap_push(bencher: &mut Bencher) {
		let sample = setup_sample();
		bencher.iter(|| {
			let mut bh = BinaryHeap::new();
			for &key in sample.iter() {
				black_box(bh.push(key));
			}
		});
	}

	#[bench]
	fn pairing_heap_pop(bencher: &mut Bencher) {
		let mut ph = PairingHeap::new();
		for key in setup_sample().into_iter() {
			ph.push(key);
		}
		bencher.iter(|| {
			let mut ph = ph.clone();
			while let Some(_) = black_box(ph.pop()) {}
		});
	}

	#[bench]
	fn binary_heap_pop(bencher: &mut Bencher) {
		let mut bh = BinaryHeap::new();
		for key in setup_sample().into_iter() {
			bh.push(key);
		}
		bencher.iter(|| {
			let mut bh = bh.clone();
			while let Some(_) = black_box(bh.pop()) {}
		});
	}

    #[bench]
    fn binary_heap_timeout(bencher: &mut Bencher) {
        let mut bh = BinaryHeap::new();
		let mut n = 0;
        for _ in 0..1500 {
            bh.push((-n, -n));
            n += 1;
        }
		bencher.iter(|| {
			bh.pop();
            bh.push((-n, -n));
            n += 1;
		});
    }

    #[bench]
    fn pairing_heap_timeout(bencher: &mut Bencher) {
		let mut ph = PairingHeap::new();
		let mut n = 0;
        for _ in 0..1500 {
            ph.push((-n, -n));
            n += 1;
        }
		bencher.iter(|| {
			ph.pop();
            ph.push((-n, -n));
            n += 1;
		});
    }
}