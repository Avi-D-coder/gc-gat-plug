#![allow(incomplete_features)]
#![feature(specialization)]
#![feature(marker_trait_attr)]
#![feature(generic_associated_types)]
#![feature(negative_impls)]
#![feature(optin_builtin_traits)]

use auto_traits::NoGc;
use std::marker::PhantomData;

fn main() {
    println!("Hello, world!");
}

pub trait Plug {
    type T<T>: UnPlug<T = Self>;
}

pub trait UnPlug {
    type T: Plug;
}

pub trait PlugLife {
    type T<'l>: 'l + UnPlugLife<T = Self>;
}

pub trait UnPlugLife {
    type T: PlugLife;
}

pub struct P<T: 'static>(T);
impl<T: 'static> PlugLife for P<T> {
    type T<'l> = P<T>;
}

impl<T: 'static> UnPlugLife for P<T> {
    type T = P<T>;
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

#[test]
fn unify_test() {
    fn foo<A, B: Id<A>>() {}
    foo::<usize, usize>();
    foo::<Gc<usize>, Gc<usize>>();

    fn lifes<'a, 'b, T: for<'l> PlugLife>() {
        foo::<Ty<'b, Gc<'a, usize>>, Gc<'b, usize>>();
        // let a: Gc<'a, usize> = Gc(&1);
        // let b: Gc<'b, usize> = transmute_lifetime(a);
        // foo::<>();
        // foo::<Gc<'a, usize>, Gc<'a, Ty<'a, usize>>>();
    }
    // foo::<Gc<usize>, Gc<Ty<Ty<String>>>>();
}

pub unsafe trait Id<T> {}
unsafe impl<T> Id<T> for T {}

#[marker]
pub unsafe trait TyEq<B> {}
unsafe impl<T> TyEq<T> for T {}
unsafe impl<A, B> TyEq<B> for A
where
    Static<A>: Id<Static<B>>,
    A: UnPlugLife,
    B: UnPlugLife,
{
}
unsafe impl<A, B> TyEq<B> for A
where
    Static<A>: Id<Static<B>>,
    A: UnPlugLife,
    B: UnPlugLife,
{
}
unsafe impl<A, B> TyEq<B> for A
where
    A::T<'static>: Id<Static<B>>,
    A: PlugLife,
    B: UnPlugLife,
{
}
unsafe impl<A, B> TyEq<B> for A
where
    B::T<'static>: Id<Static<A>>,
    A: UnPlugLife,
    B: PlugLife,
{
}
// unsafe impl<A, B> TyEq<B> for A
// where
//     TyEq<list::ListL<<T as UnPlugLife>::T>>` is not implemented for `list::List<'_, <<T as UnPlugLife>::T as PlugLife>::T<'_>>
// {}

// pub trait Trace {}

pub type Ty<'r, T> = <<T as UnPlugLife>::T as PlugLife>::T<'r>;
pub type Static<T> = <<T as UnPlugLife>::T as PlugLife>::T<'static>;
pub type Of<T> = <T as UnPlugLife>::T;

pub struct Arena<T: PlugLife>(Vec<T::T<'static>>);

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

    impl<T: PlugLife> ElemL<T> {
        pub fn gc<'r, 'a: 'r>(
            arena: &'a Arena<Self>,
            next: impl TyEq<ListL<T>>,
            value: impl TyEq<T>,
        ) -> Gc<'r, Elem<'r, <T as PlugLife>::T<'r>>> {
            let e = todo!();
        }
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

    impl<'o, T: Clone + UnPlugLife> List<'o, T> {
        /// Prepend `value` to a list.
        /// The arguments are in reverse order.
        pub fn cons<'r, 'a: 'r>(
            self,
            value: T,
            arena: &'a Arena<ElemL<Of<T>>>,
        ) -> List<'r, Ty<'r, T>>
        where
            T: PartialEq<Ty<'r, T>>,
        {
            let val = value.clone();
            let e: Gc<Elem<Ty<'r, T>>> = ElemL::<Of<T>>::gc(arena, self, value);
            match e {
                Gc(Elem { next, value: v }) => {
                    if val == *v {
                    } else {
                    }
                }
            };
            List::from(e)
            // todo!()
        }

        pub fn insert<'r, 'a: 'r>(
            self,
            index: usize,
            arena: &'a Arena<ElemL<Of<T>>>,
        ) -> List<'r, Ty<'r, T>>
where
    // T::L<'static>: GC + Clone + Sized + ID<<T as Life>::L<'static>>,
    // T::L<'a>: GC + Sized,
    // T::L<'r>: GC + Sized,
        {
            let Gc(Elem { value, next }) = self.0.unwrap();
            let next = next.insert(index - 1, arena);

            List::from(ElemL::<Of<T>>::gc(arena, next, value.clone()))
        }
    }
}
