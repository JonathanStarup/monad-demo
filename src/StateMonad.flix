use List.{append, reverse};

// The delayed functor/applicative/monad classes

pub class DFunctor[m: Type -> Bool -> Type] {
    pub def map[a: Type, b: Type, ef1: Bool, ef2: Bool]
            (f: a -> b & ef1, x: m[a, ef2]): m[b, ef1 and ef2]
}

pub class DApplicative[m: Type -> Bool -> Type] with DFunctor[m] {

    pub def point(x: a): m[a, Pure]

    pub def ap[a: Type, b: Type, ef1: Bool, ef2: Bool, ef3: Bool]
            (f: m[a -> b & ef1, ef2], x: m[a, ef3]):
            m[b, ef1 and ef2 and ef3]

}

pub class DMonad[m: Type -> Bool -> Type] with DApplicative[m] {
    pub def flatMap[a: Type, b: Type, ef1: Bool, ef2: Bool, ef3: Bool]
            (f: a -> m[b, ef1] & ef2, x: m[a, ef3]):
            m[b, ef1 and ef2 and ef3]
}


namespace StateMonadDemo {

    // 1st version: Naive pure state by explicit pass.

    pub def reverseWithCount(count: Int32, l: List[a]): (Int32, List[a]) =
        (count+1, reverse(l))

    pub def appendReverseWithCount(count: Int32, l1: List[a], l2: List[a]): (Int32, List[a]) = {
        let (count1, revl1) = reverseWithCount(count, l1);
        let (count2, revl2) = reverseWithCount(count1, l2);
        (count2+1, revl1 `append` revl2)
    }
    
    pub def append3ReverseWithCount
            (count: Int32, l1: List[a], l2: List[a], l3: List[a]):
            (Int32, List[a]) =
    {
        let (count1, revl1) = reverseWithCount(count, l1);
        let (count2, revl2) = reverseWithCount(count1, l2);
        let (count3, revl3) = reverseWithCount(count2, l3);
        (count3+1, revl1 `append` revl2 `append` revl3)
    }

    // Store the stateful operation to evaluate later.

    pub enum StateMonad[state: Type, a: Type, ef: Bool] {
        case StateMonad(state -> (state, a) & ef)
    }

    // Assume the monad operations

    namespace StateMonad {
        use StateMonadDemo.StateMonad;
        use StateMonadDemo.StateMonad.StateMonad;

        pub def point(x: a): StateMonad[s, a, true] = ???

        pub def flatMap
                (f: a -> StateMonad[s, b, ef1] & ef2, x: StateMonad[s, a, ef3]):
                StateMonad[s, b, ef1 and ef2 and ef3] = ???

        pub def runWith(init: s, m: StateMonad[s, a, ef]): (s, a) & ef =
            let StateMonad(f) = m;
            f(init)

    }

    // 2nd version: The improved functions

    pub def reverseWithCount2(l: List[a]): StateMonad[Int32, List[a], Pure] = {
        StateMonad(s -> (s+1, reverse(l)))
    }

    pub def appendReverseWithCount2(l1: List[a], l2: List[a]): StateMonad[Int32, List[a], Pure] = {
        use StateMonadDemo/StateMonad.flatMap;
        reverseWithCount2(l1) |> flatMap(revl1 ->
            reverseWithCount2(l2) |> flatMap(revl2 ->
                StateMonad(count -> (count+1, revl1 `append` revl2))
            )
        )
    }

    pub def append3ReverseWithCount2
            (l1: List[a], l2: List[a], l3: List[a]):
            StateMonad[Int32, List[a], Pure] =
    {
        use StateMonadDemo/StateMonad.flatMap;
        reverseWithCount2(l1) |> flatMap(revl1 ->
            reverseWithCount2(l2) |> flatMap(revl2 ->
                reverseWithCount2(l3) |> flatMap(revl3 ->
                    StateMonad(count -> (count+1, revl1 `append` revl2 `append` revl3))
                )
            )
        )
    }

    // The delayed effect functor/applicative/monad and their implementations

    instance DFunctor[StateMonad[s]] {
        pub def map
                (f: a -> b & ef1, x: StateMonad[s, a, ef2]):
                StateMonad[s, b, ef1 and ef2] =
        {
            StateMonad(s1 ->
                let StateMonad(fn) = x;
                let (s2, res) = fn(s1);
                (s2, f(res))
            )
        }
    }

    instance DApplicative[StateMonad[s]] {
    
        pub def point(x: a): StateMonad[s][a, true] =
            StateMonad(s -> (s, x))
    
        pub def ap
                (f: StateMonad[s, a -> b & ef1, ef2], x: StateMonad[s, a, ef3]):
                StateMonad[s][b, ef1 and ef2 and ef3] =
        {
            StateMonad(s1 -> (
                let StateMonad(ff) = f;
                let StateMonad(xx) = x;
                let (s2, fActual) = ff(s1);
                let (s3, xActual) = xx(s2);
                (s3, fActual(xActual))
            ))
        }
    
    }

    instance DMonad[StateMonad[s]] {
    
        pub def flatMap
                (f: a -> StateMonad[s, b, ef1] & ef2, x: StateMonad[s, a, ef3]):
                StateMonad[s, b, ef1 and ef2 and ef3] =
        {
            StateMonad(s1 -> (
                let StateMonad(xx) = x;
                let (s2, xActual) = xx(s1);
                let StateMonad(fx) = f(xActual);
                fx(s2)
            ))
        }
    
    }

    // Helper functions

    pub def get(): StateMonad[s, s, Pure] =
        StateMonad(s -> (s, s))
    
    pub def put(x: s): StateMonad[s, Unit, Pure] =
        StateMonad(_ -> (x, ()))

    pub def modify(f: s -> s & ef): StateMonad[s, Unit, ef] =
        use DMonad.flatMap;
        use DFunctor.map;
        get() |> map(f) |> flatMap(put)
    
    // 3rd version: with nice methods

    pub def reverseWithCount3(l: List[a]): StateMonad[Int32, List[a], Pure] = {
        use DApplicative.point;
        use DFunctor.map;
        // could be shorter with productRight from applicative
        modify(s -> s+1) |> map(_ -> reverse(l))
    }

    pub def appendReverseWithCount3(l1: List[a], l2: List[a]): StateMonad[Int32, List[a], Pure] = {
        use DMonad.flatMap;
        use DFunctor.map;
        let* revl1 = reverseWithCount3(l1);
        let* revl2 = reverseWithCount3(l2);
        modify(s -> s+1) |>
            map(_ -> revl1 `append` revl2)
    }

    pub def append3ReverseWithCount3
            (l1: List[a], l2: List[a], l3: List[a]):
            StateMonad[Int32, List[a], Pure] =
    {
        use DMonad.flatMap;
        use DFunctor.map;
        let* revl1 = reverseWithCount3(l1);
        let* revl2 = reverseWithCount3(l2);
        let* revl3 = reverseWithCount3(l3);
        modify(s -> s+1) |>
            map(_ -> revl1 `append` revl2 `append` revl3)
    }

    pub def test(): Unit & Impure = {
        use StateMonadDemo/StateMonad.runWith;
        let l1 = 1 :: 2 :: Nil;
        let l2 = 2 :: 3 :: Nil;
        let l3 = 5 :: 4 :: Nil;
        append3ReverseWithCount3(l1, l2, l3) |>
            runWith(0) |>
            println 
    }
    
    
}


/// namespace RandomMonadDemo {

///     pub enum MaxBound {
///         case Exclusive, Inclusive
///     }

///     namespace MaxBound {
///         use RandomMonadDemo.MaxBound;
///         use RandomMonadDemo.MaxBound.Exclusive;
///         use RandomMonadDemo.MaxBound.Inclusive;

///         pub def isExclusive(m: MaxBound): Bool = match m {
///             case Exclusive => true
///             case Inclusive => false
///         }
///     }

///     pub enum RandomMonad[a] {
///         case RandomMonad({min :: Int32}, Int32, MaxBound, Int32 -> (Int32, a))
///     }

///     namespace RandomMonad {
///         use RandomMonadDemo.RandomMonad;
///         use RandomMonadDemo.RandomMonad.RandomMonad;
///         use RandomMonadDemo.MaxBound;
///         use RandomMonadDemo/MaxBound.isExclusive;

///         pub def nextInt(state: {state :: Int32}, min: {min :: Int32}, max: Int32, m: MaxBound): Int32 = {
///             let range0state = state.state - min.min;
///             let range0max = max - min.min + (if (isExclusive(m)) 0 else 1);
///             let shuffle = (range0state * 13 + 17) mod range0max;
///             shuffle + min.min
///         }

///         pub def newWithSeed
///                 (seed: {seed :: Int32}, min: {min :: Int32}, max: Int32, m: MaxBound):
///                 RandomMonad[Unit] =
///         {
///             RandomMonad({min = min.min}, max, m, initRoll -> (initRoll, ()))
///         }

///     }

///     pub def test(): Unit = {
///         use RandomMonadDemo/RandomMonad.nextInt;
///         use RandomMonadDemo.MaxBound.Exclusive;
///         use RandomMonadDemo/RandomMonad.newWithSeed;

///         let rand = newWithSeed({seed = 42}, {min = 1}, 6, Exclusive);
///         ???
///     }

/// }
