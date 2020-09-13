#![allow(incomplete_features)]
#![feature(specialization)]
#![feature(marker_trait_attr)]
#![feature(generic_associated_types)]
#![feature(negative_impls)]
#![feature(optin_builtin_traits)]
#![feature(const_panic)]
#![feature(const_trait_impl)]
#![feature(const_trait_bound_opt_out)]
#![feature(const_fn)]
#![feature(const_type_name)]

extern crate static_assertions as sa;

fn main() {}

use std::{
    any::{self, TypeId},
    cell::UnsafeCell,
    mem::{self, transmute, transmute_copy},
    ptr,
};

pub struct PhantomGc;
pub unsafe auto trait NoGc {}
impl<'r, T> !NoGc for Gc<'r, T> {}
impl !NoGc for PhantomGc {}

#[derive(Debug, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct Gc<'r, T>(&'r T);
impl<'r, T> Copy for Gc<'r, T> {}
impl<'r, T> Clone for Gc<'r, T> {
    fn clone(&self) -> Self {
        *self
    }
}

pub struct Arena<A>(UnsafeCell<Vec<A>>);

impl<A> Default for Arena<A> {
    fn default() -> Self {
        Arena(UnsafeCell::new(Vec::new()))
    }
}

impl<A> Arena<A> {
    fn gc<'r, 'a: 'r, T, R: 'r>(&'a self, t: T) -> Gc<'r, R>
    where
        A: TypeEq<T> + TypeEq<R>,
    {
        let _ = <A as TypeEq<T>>::TYPE_NAME_EQ;
        let _ = <A as TypeEq<R>>::TYPE_NAME_EQ;
        unsafe {
            let v = &mut *self.0.get();
            v.push(transmute_copy(&t));
            Gc(&*(v.last().unwrap() as *const A as *const _))
        }
    }
}

trait Static {
    type S: 'static;
}

type Of<T> = <T as Static>::S;

impl<T: 'static + NoGc> Static for T {
    type S = T;
}

unsafe trait CoerceLife<'b, 'a: 'b, A: 'a>: 'b + Sized + TypeEq<A> {
    #[inline(always)]
    fn coerce_life(a: A) -> Self {
        let _ = Self::TYPE_NAME_EQ;

        let b = unsafe { ptr::read(&a as *const _ as *const _) };
        mem::forget(a);
        b
    }
}

/// Implemented for a type regardless of lifetime.
/// This will not generate an error a mismatched types error until you write `let _ = Self::TYPE_NAME_EQ;`
trait TypeEq<A> {
    const TYPE_NAME_EQ: bool;
}
impl<A, B> TypeEq<A> for B {
    default const TYPE_NAME_EQ: bool = if type_name_eq::<&A, &Self>() {
        true
    } else {
        panic!("type mismatch") //~ [rustc const_err] [E] any use of this value will cause an error `#[deny(const_err)]` on by default
    };
}

impl<'a, 'b, A: 'a, B: 'b> TypeEq<Gc<'a, A>> for Gc<'b, B> {
    default const TYPE_NAME_EQ: bool = if type_name_eq::<&A, &Self>() {
        true
    } else {
        panic!("type mismatch") //~ [rustc const_err] [E] any use of this value will cause an error `#[deny(const_err)]` on by default
    };
}

pub const fn type_name_eq<A, B>() -> bool {
    let a = any::type_name::<A>().as_bytes();
    let b = any::type_name::<B>().as_bytes();
    if a.len() != b.len() {
        false
    } else {
        let mut i = 0;
        while i < a.len() {
            if a[i] != b[i] {
                return false;
            }

            i += 1;
        }

        true
    }
}

#[test]
fn type_eq_ref_test() {
    assert!(!type_name_eq::<usize, &usize>());
}

unsafe impl<'b, 'a: 'b, A: 'a, B: 'b> CoerceLife<'b, 'a, Gc<'a, A>> for Gc<'b, B> where
    Self: TypeEq<Gc<'a, A>>
{
}

#[test]
fn type_eq_test() {
    // Gc::<usize>::coerce_life(Gc(&1isize)); //~ Err
}

#[test]
fn life_times_test() {
    fn good<'a>(n: usize, a: &'a Arena<usize>) -> Gc<'a, usize> {
        Gc::coerce_life(a.gc::<usize, usize>(n))
    }

    fn good2<'r, 'a: 'r, T: Static>(n: T, a: &'a Arena<T::S>) -> Gc<'r, T> {
        let n: Gc<'r, T> = a.gc(n);
        Gc::coerce_life(n)
    }

    fn good3<'s, 'b: 's, T>(t: &'s T) -> &'b T {
        // Gc::coerce_life(Gc(t)).0 //~ [rustc E0495] [E] cannot infer an appropriate lifetime for lifetime parameter `'r` due to conflicting requirements
        unreachable!()
    }

    fn good4<'s, 'b: 's, T>(t: &'b T) -> &'s T {
        Gc::coerce_life(Gc(t)).0
    }

    fn good5<'s, 'b: 's, T>(t: &'b T) -> &'s T
    where
        for<'l> &'l T: Static,
    {
        let a = Arena::default();
        good2(t, &a).0
    }

    fn good6<'s, 'b: 's, T>(t: &'s T) -> &'b T
    where
        for<'l> &'l T: Static,
    {
        let a: Arena<<&T as Static>::S> = Arena::default();
        // good2(t, &a).0 //~ [rustc E0495] [E] cannot infer an appropriate lifetime due to conflicting requirements expected `&T` found `&'s T`
        unreachable!()
    }
}

mod list {
    use super::{Arena, CoerceLife, Gc, Of, Static};
    use std::{
        mem::{self, transmute},
        ptr,
    };

    #[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd)]
    enum List<'r, T> {
        Cons(T, Gc<'r, List<'r, T>>),
        Nil,
    }

    impl<'l, T: Static + Clone> List<'l, T> {
        fn cons<'r, 'a: 'r, R>(
            t: T,
            next: Gc<'l, List<'l, T>>,
            arena: &'a Arena<T::S>,
        ) -> Gc<'r, List<'r, R>> {
            arena.gc(List::Cons(t, next))
        }

        pub fn insert<'r, 'a: 'r, R>(
            list: Gc<List<T>>,
            index: usize,
            t: T,
            arena: &'a Arena<Of<List<T>>>,
        ) -> Gc<'r, List<'r, R>> {
            if index == 0 {
                arena.gc(List::Cons(t, list))
            } else {
                match list {
                    Gc(List::Cons(v, next)) => arena.gc(List::Cons(
                        v.clone(),
                        List::insert(*next, index - 1, t, arena),
                    )),
                    Gc(List::Nil) => panic!("list is {} elemements too short", index),
                }
            }
        }
    }

    #[test]
    fn insert_test() {
        let a: Arena<<List<usize> as Static>::S> = Arena::default();
        let l: Gc<List<usize>> = a.gc(List::<usize>::Nil);

        let i: Gc<List<usize>> = List::insert(l, 0, 1, &a);
    }

    impl<'r, T: Static> Static for List<'r, T> {
        type S = List<'static, T::S>;
    }

    struct ListT<'r, T>(Option<Gc<'r, Elem<'r, T>>>)
    where
        T: 'r;

    #[derive(Clone)]
    struct Elem<'r, T>
    where
        T: 'r,
    {
        next: ListT<'r, T>,
        value: T,
    }

    impl<'r, T: Copy> Copy for Elem<'r, T> {}

    impl<'r, T> Copy for ListT<'r, T> {}
    impl<'r, T> Clone for ListT<'r, T> {
        fn clone(&self) -> Self {
            *self
        }
    }

    impl<'r, T: Static> Static for ListT<'r, T> {
        type S = ListT<'static, T::S>;
    }
    impl<'r, T: Static> Static for Elem<'r, T> {
        type S = Elem<'static, T::S>;
    }

    impl<'r, T: 'r + Static + Clone> ListT<'r, T> {
        /// Inserts an element at position `index`.
        /// This is equivalent `Vec::insert` not Haskell's `insert :: Ord a => a -> [a] -> [a]`.
        ///
        /// # Panics
        ///
        /// Panics if `index > len`.
        /// This function is recursive and may cause a stack overflow.
        ///
        /// TODO Replace with non recursive variant.
        pub fn insert<'a: 'r>(
            self,
            index: usize,
            t: T,
            arena: &'a Arena<Of<Elem<T>>>,
        ) -> ListT<'r, T> {
            let Gc(Elem { next, value }) = self.0.unwrap();
            let value: T = value.clone();

            let next: ListT<'r, T> = next.insert(index - 1, t, arena);

            ListT(Some(arena.gc(Elem { next, value })))
        }

        pub fn insert_mark<'n, 'a: 'n, N>(
            self,
            index: usize,
            t: T,
            arena: &'a Arena<Of<Elem<T>>>,
        ) -> ListT<'n, N> {
            let Gc(Elem { next, value }) = self.0.unwrap();
            let value: T = value.clone();

            let next = next.insert(index - 1, t, arena);

            ListT(Some(arena.gc(Elem { next, value })))
        }
    }
}

mod alloc {
    use crate::{Arena, Gc, NoGc, Of, Static};

    pub unsafe trait Alloc<'n, O, N: 'n> {
        /// Create and allocate a new `Gc<T>`.
        /// This has the effect of marking `T`'s decedents live for the lifetime of the Arena `'a`.
        ///
        /// If `T : Copy` & `size_of::<T>() > 8`, you should use `self.gc_copy(&T)` instead.
        fn gc_mark<'a: 'n>(&'a self, t: O) -> Gc<'n, N>;
        // TODO gc_*
    }

    unsafe impl<'n, A, O, N: 'n> Alloc<'n, O, N> for Arena<A> {
        default fn gc_mark<'a: 'n>(&'a self, t: O) -> Gc<'n, N> {
            todo!()
        }
    }

    unsafe impl<'n, A: NoGc + 'static> Alloc<'n, A, A> for Arena<A> {
        fn gc_mark<'a: 'n>(&'a self, t: A) -> Gc<'n, A> {
            todo!()
        }
    }

    pub unsafe trait Trace: Immutable {
        fn fields(s: &Self, offset: u8, grey_fields: u8) -> u8;
    }

    struct List<'r, T>(Option<Gc<'r, Elem<'r, T>>>)
    where
        T: 'r;

    #[derive(Clone)]
    struct Elem<'r, T>
    where
        T: 'r,
    {
        next: List<'r, T>,
        value: T,
    }

    impl<'r, T: Copy> Copy for Elem<'r, T> {}

    impl<'r, T> Copy for List<'r, T> {}
    impl<'r, T> Clone for List<'r, T> {
        fn clone(&self) -> Self {
            *self
        }
    }

    impl<'r, T: Static> Static for List<'r, T> {
        type S = List<'static, T::S>;
    }
    impl<'r, T: Static> Static for Elem<'r, T> {
        type S = Elem<'static, T::S>;
    }

    impl<'r, T: 'r + Static + Clone> List<'r, T> {
        /// Inserts an element at position `index`.
        /// This is equivalent `Vec::insert` not Haskell's `insert :: Ord a => a -> [a] -> [a]`.
        ///
        /// # Panics
        ///
        /// Panics if `index > len`.
        /// This function is recursive and may cause a stack overflow.
        ///
        /// TODO Replace with non recursive variant.
        pub fn insert<'a: 'r>(
            self,
            index: usize,
            t: T,
            arena: &'a Arena<Of<Elem<T>>>,
        ) -> List<'r, T> {
            let Gc(Elem { next, value }) = self.0.unwrap();
            let value: T = value.clone();

            let next: List<'r, T> = next.insert(index - 1, t, arena);

            List(Some(arena.gc(Elem { next, value })))
        }

        pub fn insert_mark<'n, 'a: 'n, N>(
            self,
            index: usize,
            t: T,
            arena: &'a Arena<Of<Elem<T>>>,
        ) -> List<'n, N> {
            let Gc(Elem { next, value }) = self.0.unwrap();
            let value: T = value.clone();

            let next = next.insert(index - 1, t, arena);

            List(Some(arena.gc(Elem { next, value })))
        }
    }
}
