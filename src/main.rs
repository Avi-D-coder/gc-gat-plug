#![allow(incomplete_features)]
#![feature(specialization)]
#![feature(marker_trait_attr)]
#![feature(generic_associated_types)]
#![feature(negative_impls)]
#![feature(optin_builtin_traits)]
#![feature(dropck_eyepatch)]

use auto_traits::NoGc;
use std::marker::PhantomData;

fn main() {
    println!("Hello, world!");
}

pub trait PlugL<'a>: PlugLife {
    type TL;
}

impl<'a, T: PlugLife> PlugL<'a> for T {
    type TL = Self::T<'a>;
}

pub trait Plug {
    type T<T>: UnPlug<T = Self>;
}

pub trait UnPlug {
    type T;
    type A;
}

pub trait PlugLife {
    type T<'l>: 'l + UnPlugLife<T = Self>;
}

pub trait UnPlugLife {
    type T: PlugLife;
}

impl PlugLife for usize {
    type T<'l> = usize;
}

impl UnPlugLife for usize {
    type T = usize;
}

/// Realy `Gc<'r, T>(&'r T<'r>);`
pub struct Gc<'r, T>(&'r T);
impl<'r, T> Copy for Gc<'r, T> {}
impl<'r, T> Clone for Gc<'r, T> {
    fn clone(&self) -> Self {
        *self
    }
}

pub struct GcL<T>(PhantomData<T>);
impl<T: PlugLife> PlugLife for GcL<T> {
    type T<'l> = Gc<'l, <T as PlugLife>::T<'l>>;
}
impl<'r, T: UnPlugLife> UnPlugLife for Gc<'r, T> {
    type T = GcL<<T as UnPlugLife>::T>;
}

pub type Life<'r, T> = <<T as UnPlugLife>::T as PlugLife>::T<'r>;

pub struct Arena<#[may_dangle] A>(Vec<A>);

impl<#[may_dangle] T: UnPlugLife> Arena<T> {
    pub fn gc<'r>(&'r self, t: T) -> Gc<'r, Life<'r, T>> {
        todo!()
    }

    pub fn new() -> Arena<T> {
        todo!()
    }

    pub fn mark<'n>(&'n self, o: Gc<'_, T>) -> Gc<'n, Life<'n, T>> {
        unsafe { std::mem::transmute(o) }
    }
}

mod auto_traits {
    use super::*;
    use std::cell::UnsafeCell;

    pub unsafe auto trait NoGc {}
    impl<'r, T> !NoGc for Gc<'r, T> {}
    // unsafe impl<'r, T: NoGc> NoGc for Box<T> {}

    pub trait HasGc {
        const HAS_GC: bool;
    }

    impl<T> HasGc for T {
        default const HAS_GC: bool = true;
    }

    impl<T: NoGc> HasGc for T {
        const HAS_GC: bool = false;
    }

    /// Shallow immutability
    pub unsafe auto trait Immutable {}
    impl<T> !Immutable for &mut T {}
    impl<'r, T> !Immutable for &'r T {}
    impl<T> !Immutable for UnsafeCell<T> {}
    unsafe impl<T> Immutable for Box<T> {}
    unsafe impl<'r, T> Immutable for Gc<'r, T> {}

    /// Should be implemented with each `Trace` impl.
    pub auto trait NotDerived {}
    impl<'l, T> !NotDerived for Gc<'l, T> {}
}

// #[cfg(off)]
mod list {
    use super::*;

    pub struct List<'r, T>(Option<Gc<'r, Elem<'r, T>>>);
    #[derive(Clone)]
    pub struct Elem<'r, T> {
        next: List<'r, T>,
        value: T,
    }

    pub struct ListL<T>(PhantomData<T>);
    pub struct ElemL<T>(PhantomData<T>);

    impl<T: PlugLife> PlugLife for ListL<T> {
        type T<'l> = List<'l, <T as PlugLife>::T<'l>>;
    }
    impl<'r, T: UnPlugLife> UnPlugLife for List<'r, T> {
        type T = ListL<<T as UnPlugLife>::T>;
    }
    impl<T: PlugLife> PlugLife for ElemL<T> {
        type T<'l> = Elem<'l, <T as PlugLife>::T<'l>>;
    }
    impl<'r, T: UnPlugLife> UnPlugLife for Elem<'r, T> {
        type T = ElemL<<T as UnPlugLife>::T>;
    }

    impl<'r, T> Clone for List<'r, T> {
        fn clone(&self) -> Self {
            *self
        }
    }
    impl<'r, T> Copy for List<'r, T> {}
    impl<'r, T: Copy> Copy for Elem<'r, T> {}

    impl<'r, T> From<Gc<'r, Elem<'r, T>>> for List<'r, T> {
        fn from(e: Gc<'r, Elem<'r, T>>) -> Self {
            List(Some(e))
        }
    }

    impl<'o, T: UnPlugLife> List<'o, T> {
        /// Prepend `value` to a list.
        /// The arguments are in reverse order.
        pub fn cons<'r, 'a: 'r>(
            self,
            value: T,
            arena: &'a Arena<Elem<T>>,
        ) -> List<'r, Life<'r, T>> {
            let elem: Elem<'o, T> = Elem { next: self, value };
            let e: Gc<'r, Life<'r, Elem<T>>> = arena.gc(elem);
            //~                                      ^^
            // [rustc E0495] [E] cannot infer an appropriate lifetime due to conflicting requirements
            // expected `Elem<'_, _>`
            //    found `Elem<'o, _>`
            // expected `Gc<'r, Elem<'r, <<T as UnPlugLife>::T as PlugLife>::T<'r>>>`
            //    found `Gc<'_, Elem<'_, <<T as UnPlugLife>::T as PlugLife>::T<'_>>>`
            List::from(e)
        }
    }

    #[test]
    fn function_name_test() {
       fn foo<'a, 'b, T: UnPlugLife + Eq>(a: Life<'a, T>, b: Life<'b, T>) {
           let mut v = a;
           v = b; //~ [rustc E0623] [E] lifetime mismatch ...but data from `a` flows into `b` here

           a == b; 
           //^~ [rustc E0369] [E] binary operation `==` cannot be applied to type `<<T as UnPlugLife>::T as PlugLife>::T<'a>`
           //   the trait `std::cmp::PartialEq` is not implemented for `<<T as UnPlugLife>::T as PlugLife>::T<'a>`
       } 
    }
}
