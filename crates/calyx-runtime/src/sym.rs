//! Interned identifier names.

use std::cell::RefCell;
use std::fmt;
use std::rc::Rc;

use rustc_hash::FxHashMap;

/// An interned name. Comparing and hashing symbols is a single integer
/// operation; the text is recovered with [`Sym::as_str`].
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Sym(u32);

#[derive(Default)]
struct Interner {
    names: Vec<Rc<str>>,
    ids: FxHashMap<Rc<str>, u32>,
}

thread_local! {
    static INTERNER: RefCell<Interner> = RefCell::new(Interner::default());
}

impl Sym {
    pub fn new(s: &str) -> Sym {
        INTERNER.with(|i| {
            let mut i = i.borrow_mut();
            if let Some(&id) = i.ids.get(s) {
                return Sym(id);
            }
            let id = i.names.len() as u32;
            let rc: Rc<str> = Rc::from(s);
            i.names.push(rc.clone());
            i.ids.insert(rc, id);
            Sym(id)
        })
    }

    pub fn as_rc(self) -> Rc<str> {
        INTERNER.with(|i| i.borrow().names[self.0 as usize].clone())
    }

    pub fn as_str(self) -> String {
        self.as_rc().to_string()
    }

    pub fn index(self) -> u32 {
        self.0
    }
}

impl fmt::Debug for Sym {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.as_rc())
    }
}

impl fmt::Display for Sym {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.as_rc())
    }
}

impl From<&str> for Sym {
    fn from(s: &str) -> Sym {
        Sym::new(s)
    }
}
