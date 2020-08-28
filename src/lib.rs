// use std::cell::{Ref, RefCell};
use std::sync::{Arc, Mutex};
use std::cmp;

type BareTree<T> = Arc<Mutex<Node<T>>>;
type Tree<T> = Option<BareTree<T>>;

#[derive(Clone, Debug, PartialEq)]
pub enum Color {
    Red,
    Black,
}

#[derive(PartialEq)]
enum RBOperation {
    LeftNode,
    RightNode,
}

#[derive(PartialEq)]
enum Rotation {
    Left,
    Right,
}

pub struct Node<T: Ord> {
    pub color: Color,
    pub val: T,
    pub parent: Tree<T>,
    left: Tree<T>,
    right: Tree<T>,
}

impl<T: Ord> PartialEq for Node<T> {
    fn eq(&self, other: &Node<T>) -> bool {
        self.val == other.val
    }
}

#[derive(Clone)]
pub struct RedBlackTree<T: Ord> {
    root: Tree<T>,
    pub length: u64,
}

impl<T: Ord> Node<T>{
    pub fn new(val: T) -> Tree<T> {
        Some(Arc::new(Mutex::new(Node {
            color: Color::Red,
            val: val,
            parent: None,
            left: None,
            right: None,
        })))
    }
}

impl<T: Ord + Clone + std::fmt::Debug> RedBlackTree<T> {
    pub fn new(val: T) -> RedBlackTree<T> {
        RedBlackTree{
            root: Node::new(val),
            length: 1,
        }
    }

    pub fn add(&mut self, val: T) {
        if let Some(root) = &self.root {
            let root_clone = Arc::clone(&root);
            let new_tree = self.add_r(Some(root_clone), val);
            self.length += 1;
            self.root = self.fix_tree(new_tree.1)
        }
    }

    fn check(&self, a: &T, b: &T) -> RBOperation {
        if a <= b {
            RBOperation::LeftNode
        } else {
            RBOperation::RightNode
        }
    }

    fn add_r(&mut self, mut node: Tree<T>, val: T) -> (Tree<T>, BareTree<T>) {
        if let Some(n) = node.take() {
            let new: BareTree<T>;
            let mut node_guard = n.lock().unwrap();
            let current_value = node_guard.val.clone();

            match self.check(&current_value, &val) {
                RBOperation::LeftNode => {
                    let left = node_guard.left.clone();
                    let new_tree = self.add_r(left, val);
                    new = new_tree.1;
                    let new_tree = new_tree.0.unwrap();
                    new_tree.lock().unwrap().parent = Some(n.clone());
                    node_guard.left = Some(new_tree);
                }

                RBOperation::RightNode => {
                    let right = node_guard.right.clone();
                    let new_tree = self.add_r(right, val);
                    new = new_tree.1;
                    let new_tree = new_tree.0.unwrap();

                    new_tree.lock().unwrap().parent = Some(n.clone());
                    node_guard.right = Some(new_tree);
                }
            }
            drop(node_guard);
            (Some(n), new)
        } else {
            let new = Node::new(val);
            (new.clone(), new.unwrap())
        }
    }

    pub fn is_a_valid_red_black_tree(&self) -> bool {
        let result = self.validate(&self.root, Color::Red, 0);
        let red_red = result.0;
        let black_height_min = result.1;
        let black_height_max = result.2;
        red_red == 0 && black_height_min == black_height_max
    }

    // red-red violations, min black-height, max-black-height
    fn validate(
        &self,
        node: &Tree<T>,
        parent_color: Color,
        black_height: usize,
    ) -> (usize, usize, usize) {
        if let Some(n) = node {
            let node_guard = n.lock().unwrap();
            let red_red = if parent_color == Color::Red && node_guard.color == Color::Red {
                1
            } else {
                0
            };
            let black_height = black_height + match node_guard.color {
                Color::Black => 1,
                _ => 0,
            };
            let l = self.validate(&node_guard.left, node_guard.color.clone(), black_height);
            let r = self.validate(&node_guard.right, node_guard.color.clone(), black_height);
            (red_red + l.0 + r.0, cmp::min(l.1, r.1), cmp::max(l.2, r.2))
        } else {
            (0, black_height, black_height)
        }
    }

    fn parent_color(&self, n: &BareTree<T>) -> Color {
        n.lock().unwrap().parent.as_ref().unwrap().lock().unwrap().color.clone()
    }

    fn fix_tree(&mut self, inserted: BareTree<T>) -> Tree<T> {
        let mut not_root = inserted.lock().unwrap().parent.is_some();

        let root = if not_root {
            let mut parent_is_red = self.parent_color(&inserted) == Color::Red;
            let mut n = inserted.clone();
            while parent_is_red && not_root {
                if let Some(uncle) = self.uncle(n.clone()) {
                    let which = uncle.1;
                    let uncle = uncle.0;

                    match which {
                        RBOperation::LeftNode => {
                            // uncle is on the left
                            let mut parent = n.lock().unwrap().parent.as_ref().unwrap().clone();
                            if uncle.is_some()
                                && uncle.as_ref().unwrap().lock().unwrap().color == Color::Red
                            {
                                let uncle = uncle.unwrap();
                                parent.lock().unwrap().color = Color::Black;
                                uncle.lock().unwrap().color = Color::Black;
                                parent.lock().unwrap().parent.as_ref().unwrap().lock().unwrap().color =
                                    Color::Red;

                                n = parent.lock().unwrap().parent.as_ref().unwrap().clone();
                            } else {
                                if self.check(&parent.lock().unwrap().val, &n.lock().unwrap().val)
                                    == RBOperation::LeftNode
                                {
                                    // do only if it's a right child
                                    let tmp = n.lock().unwrap().parent.as_ref().unwrap().clone();
                                    n = tmp;
                                    self.rotate(n.clone(), Rotation::Right);
                                    parent = n.lock().unwrap().parent.as_ref().unwrap().clone();
                                }
                                // until here. then for all black uncles
                                parent.lock().unwrap().color = Color::Black;
                                parent.lock().unwrap().parent.as_ref().unwrap().lock().unwrap().color =
                                    Color::Red;
                                let grandparent = n
                                    .lock()
                                    .unwrap()
                                    .parent
                                    .as_ref()
                                    .unwrap()
                                    .lock()
                                    .unwrap()
                                    .parent
                                    .as_ref()
                                    .unwrap()
                                    .clone();
                                self.rotate(grandparent, Rotation::Left);
                            }
                        }

                        RBOperation::RightNode => {
                            // uncle is on the right
                            let mut parent = n.lock().unwrap().parent.as_ref().unwrap().clone();

                            if uncle.is_some()
                                && uncle.as_ref().unwrap().lock().unwrap().color == Color::Red
                            {
                                let uncle = uncle.unwrap();

                                parent.lock().unwrap().color = Color::Black;
                                uncle.lock().unwrap().color = Color::Black;
                                parent.lock().unwrap().parent.as_ref().unwrap().lock().unwrap().color =
                                    Color::Red;

                                n = parent.lock().unwrap().parent.as_ref().unwrap().clone();
                            } else {
                                if self.check(&parent.lock().unwrap().val, &n.lock().unwrap().val)
                                    == RBOperation::RightNode
                                {
                                    // do only if it's a right child
                                    let tmp = n.lock().unwrap().parent.as_ref().unwrap().clone();
                                    n = tmp;
                                    self.rotate(n.clone(), Rotation::Left);
                                    parent = n.lock().unwrap().parent.as_ref().unwrap().clone();
                                }
                                // until here. then for all black uncles
                                parent.lock().unwrap().color = Color::Black;
                                parent.lock().unwrap().parent.as_ref().unwrap().lock().unwrap().color =
                                    Color::Red;
                                let grandparent = n
                                    .lock().
                                    unwrap()
                                    .parent
                                    .as_ref()
                                    .unwrap()
                                    .lock().
                                    unwrap()
                                    .parent
                                    .as_ref()
                                    .unwrap()
                                    .clone();
                                self.rotate(grandparent, Rotation::Right);
                            }
                        }
                    }
                } else {
                    break;
                }

                not_root = n.lock().unwrap().parent.is_some();
                if not_root {
                    parent_is_red = self.parent_color(&n) == Color::Red;
                }
            }
            while n.lock().unwrap().parent.is_some() {
                let t = n.lock().unwrap().parent.as_ref().unwrap().clone();
                n = t;
            }
            Some(n)
        } else {
            Some(inserted)
        };
        root.map(|r| {
            r.lock().unwrap().color = Color::Black;
            r
        })
    }

    fn rotate(&self, node: BareTree<T>, direction: Rotation) {
        match direction {
            Rotation::Right => {
                let x = node;
                let y = x.lock().unwrap().left.clone();
                x.lock().unwrap().left = match y {
                    Some(ref y) => y.lock().unwrap().right.clone(),
                    _ => None,
                };

                if y.is_some() {
                    y.as_ref().unwrap().lock().unwrap().parent = x.lock().unwrap().parent.clone();
                    if y.as_ref().unwrap().lock().unwrap().right.is_some() {
                        let r = y.as_ref().unwrap().lock().unwrap().right.clone();
                        r.unwrap().lock().unwrap().parent = Some(x.clone());
                    }
                }

                if let Some(ref parent) = x.lock().unwrap().parent {
                    let insert_direction = self.check(&parent.lock().unwrap().val, &x.lock().unwrap().val);
                    match insert_direction {
                        RBOperation::RightNode => parent.lock().unwrap().right = y.clone(),
                        RBOperation::LeftNode => parent.lock().unwrap().left = y.clone(),
                    }
                } else {
                    y.as_ref().unwrap().lock().unwrap().parent = None;
                }
                y.as_ref().unwrap().lock().unwrap().right = Some(x.clone());
                x.lock().unwrap().parent = y.clone();
            }
            Rotation::Left => {
                let x = node;
                let y = x.lock().unwrap().left.clone();
                x.lock().unwrap().right = match y {
                    Some(ref y) => y.lock().unwrap().left.clone(),
                    _ => None,
                };

                if y.is_some() {
                    y.as_ref().unwrap().lock().unwrap().parent = x.lock().unwrap().parent.clone();

                    if y.as_ref().unwrap().lock().unwrap().left.is_some() {
                        let l = y.as_ref().unwrap().lock().unwrap().left.clone();
                        l.unwrap().lock().unwrap().parent = Some(x.clone());
                    }
                }

                if let Some(ref parent) = x.lock().unwrap().parent {
                    let insert_direction = self.check(&parent.lock().unwrap().val, &x.lock().unwrap().val);

                    match insert_direction {
                        RBOperation::LeftNode => parent.lock().unwrap().left = y.clone(),
                        RBOperation::RightNode => parent.lock().unwrap().right = y.clone(),
                    }
                } else {
                    y.as_ref().unwrap().lock().unwrap().parent = None;
                }
                y.as_ref().unwrap().lock().unwrap().left = Some(x.clone());
                x.lock().unwrap().parent = y.clone();
            }
        }
    }

    fn uncle(&self, tree: BareTree<T>) -> Option<(Tree<T>, RBOperation)> {
        let current = tree.lock().unwrap();

        if let Some(ref parent) = current.parent {
            let parent = parent.lock().unwrap();

            if let Some(ref grandparent) = parent.parent {
                let grandparent = grandparent.lock().unwrap();

                match self.check(&grandparent.val, &parent.val) {
                    RBOperation::LeftNode => {
                        Some((grandparent.right.clone(), RBOperation::RightNode))
                    }
                    RBOperation::RightNode => {
                        Some((grandparent.left.clone(), RBOperation::LeftNode))
                    }
                }
            } else {
                None
            }
        } else {
            None
        }
    }

    pub fn find(&self, val: T) -> Tree<T>  {
        self.find_r(
            &self.root,
            &val,
        )
    }

    fn find_r(&self, node: &Tree<T>, val: &T) -> Tree<T>  {
        match node {
            Some(n) => {
                let n_guard = n.lock().unwrap();
                if &n_guard.val == val {
                    Some(Arc::clone(n))
                } else {
                    match self.check(&n_guard.val, val) {
                        RBOperation::LeftNode => self.find_r(&n_guard.left, val),
                        RBOperation::RightNode => self.find_r(&n_guard.right, val),
                    }
                }
            }
            _ => None,
        }
    }

    pub fn walk(&self, callback: impl Fn(&T) -> ()) {
        self.walk_in_order(&self.root, &callback);
    }

    fn walk_in_order(&self, node: &Tree<T>, callback: &impl Fn(&T) -> ()) {
        if let Some(n) = node {
            let n = n.lock().unwrap();

            self.walk_in_order(&n.left, callback);
            callback(&n.val);
            self.walk_in_order(&n.right, callback);
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::RedBlackTree;
    use std::sync::Arc;
    use std::thread;

    #[test]
    fn insert_many() {
        const N: usize = 300;

        let tree = Arc::new(RedBlackTree::new(0));

        // spawn N-1 threads to add N-1 elements to the tree (0 already in tree)
        let mut handles = vec![];
        for i in 1..N {
            handles.push(thread::spawn({
                let tree_clone = Arc::clone(&tree);
                move || {
                    tree_clone.add(i);
                }
            }));
        }

        for handle in handles {
            let _ = handle.join().unwrap();
        }

        // check that all N elements exist in tree
        for i in 0..N {
            let found = tree.find(i);
            assert_eq!(true, found.is_some());
            let node = found.unwrap();
            let val = node.lock().unwrap().val;
            assert_eq!(val, i);
        }
    }
}
