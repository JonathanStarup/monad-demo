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


namespace RandomMonadDemo {

    pub enum MaxBound {
        case Exclusive, Inclusive
    }

    pub enum Range {
        case Range(Int32, Int32, MaxBound)
    }

    namespace MaxBound {
        use RandomMonadDemo.MaxBound;
        use RandomMonadDemo.MaxBound.Exclusive;
        use RandomMonadDemo.MaxBound.Inclusive;

        pub def isExclusive(m: MaxBound): Bool = match m {
            case Exclusive => true
            case Inclusive => false
        }
    }

    type alias RandomState = {state :: Int32, range :: Range}

    pub enum RandomMonad[a: Type, ef: Bool] {
        case RandomMonad(RandomState -> (RandomState, a) & ef)
    }

    namespace RandomMonad {
        use RandomMonadDemo.RandomState;
        use RandomMonadDemo.RandomMonad;
        use RandomMonadDemo.RandomMonad.RandomMonad;
        use RandomMonadDemo.MaxBound;
        use RandomMonadDemo/MaxBound.isExclusive;
        use RandomMonadDemo.Range.Range;
        use RandomMonadDemo.Range;

        /// OBS: This is not a good random generator
        def nextIntAux(state: Int32, range: Range): {state :: Int32, roll :: Int32} = {
            let Range(min, max, maxBound) = range;
            let range0max = max - min + (if (isExclusive(maxBound)) 0 else 1);
            let newState = (state * 11 + 17) mod 507;
            let roll = (newState mod range0max) + min;
            {state = newState, roll = roll}
        }

        pub def nextInt(): RandomMonad[Int32, Pure] = {
            RandomMonad(randomState -> (
                let rollRecord = nextIntAux(randomState.state, randomState.range);
                ({state = rollRecord.state, range = randomState.range}, rollRecord.roll)
            ))
        }

        pub def run(seed: Int32, range: Range, m: RandomMonad[a, ef]): a & ef = {
            let RandomMonad(f) = m;
            let initState: RandomState = {state = seed, range = range};
            let (_, res) = f(initState);
            res
        }
    }

    instance DFunctor[RandomMonad] {
        pub def map(f: a -> b & ef1, x: RandomMonad[a, ef2]): RandomMonad[b, ef1 and ef2] = {
            RandomMonad(s1 -> (
                let RandomMonad(xx) = x;
                let (s2, xActual) = xx(s1);
                (s2, f(xActual))
            ))
        }
    }

    instance DApplicative[RandomMonad] {
    
        pub def point(x: a): RandomMonad[a, true] =
            RandomMonad(s -> (s, x))
    
        pub def ap
                (f: RandomMonad[a -> b & ef1, ef2], x: RandomMonad[a, ef3]):
                RandomMonad[b, ef1 and ef2 and ef3] =
        {
            RandomMonad(s1 -> (
                let RandomMonad(ff) = f;
                let RandomMonad(xx) = x;
                let (s2, fActual) = ff(s1);
                let (s3, xActual) = xx(s2);
                (s3, fActual(xActual))
            ))
        }
    }

    instance DMonad[RandomMonad] {
    
        pub def flatMap
                (f: a -> RandomMonad[b, ef1] & ef2, x: RandomMonad[a, ef3]):
                RandomMonad[b, ef1 and ef2 and ef3] =
        {
            RandomMonad(s1 -> (
                let RandomMonad(xx) = x;
                let (s2, xActual) = xx(s1);
                let RandomMonad(fx) = f(xActual);
                fx(s2)
            ))
        }
    
    }

    pub def test(): Float32 & Impure = {
        use RandomMonadDemo.MaxBound.Inclusive;
        use RandomMonadDemo/RandomMonad.nextInt;
        use DApplicative.point;
        use DFunctor.map;
        use DMonad.flatMap;

        let diceRange = Range(1, 6, Inclusive);
        let rolls = List.range(0, 25) |>
            List.foldLeft((m, _) -> (
                let* l = m;
                let* roll = nextInt();
                println(roll);
                (roll :: l)  |> point
            ), point(Nil) |> map(x -> x as & Impure)) |> // hack to make init a impure monad
            RandomMonadDemo/RandomMonad.run(1, diceRange);
        def div(a, b) = Int32.toFloat32(a) / Int32.toFloat32(b);
        List.sum(rolls) `div` List.length(rolls)
    }

}
