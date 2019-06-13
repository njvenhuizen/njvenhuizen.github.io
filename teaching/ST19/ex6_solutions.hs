import Data.DRS

-- Exercise 6.1

-- If a farmer owns a donkey, he feeds it.
-- ∀x∀y((farmer(x) ∧ donkey(y) ∧ own(x,y)) → feed(x,y))
discourse1 = DRS [] [Imp 
      (DRS [DRSRef "x", DRSRef "y"] [Rel (DRSRel "farmer") [DRSRef "x"],
                                    Rel (DRSRel "donkey") [DRSRef "y"],
                                    Rel (DRSRel "own") [DRSRef "x",DRSRef "y"]]) 
      (DRS [] [Rel (DRSRel "feed") [DRSRef "x",DRSRef "y"]])]

-- Exercise 6.2

-- Robin is either in love with Ted or with Barney
-- ∃x∃y∃z(=(x,robin) ∧ =(y,ted) ∧ =(z,barney) ∧ (love(x,y) ∨ love(x,z)))
discourse2 = DRS [DRSRef "x",DRSRef "y",DRSRef "z"] [
            Rel (DRSRel "=") [DRSRef "x", DRSRef "robin"],
            Rel (DRSRel "=") [DRSRef "y", DRSRef "ted"],
            Rel (DRSRel "=") [DRSRef "z", DRSRef "barney"],
            Or (DRS [] [Rel (DRSRel "love") [DRSRef "x",DRSRef "y"]]) 
               (DRS [] [Rel (DRSRel "love") [DRSRef "x",DRSRef "z"]])]

-- Barney does not seduce every girl
-- ∃x(=(x,barney) ∧ ¬∀y(girl(y) → seduce(x,y))
discourse3 = DRS [DRSRef "x"] [
            Rel (DRSRel "=") [DRSRef "x", DRSRef "barney"],
            Neg (DRS [] [Imp (DRS [DRSRef "y"] [Rel (DRSRel "girl") [DRSRef "y"]]) 
                             (DRS [] [Rel (DRSRel "seduce") [DRSRef "x", DRSRef "y"]])])]

-- Barney does not seduce every girl (different DR availability!)
-- ∃x∃y(=(x,barney) ∧ girl(y) ∧ ¬seduce(x,y))
discourse3b = DRS [DRSRef "x",DRSRef "y"] [
            Rel (DRSRel "=") [DRSRef "x", DRSRef "barney"],
            Rel (DRSRel "girl") [DRSRef "y"],
            Neg (DRS [] [Rel (DRSRel "seduce") [DRSRef "x", DRSRef "y"]])]

-- Ted meets a girl. If she forgets her umbrella, he doesn't return it.
-- ∃x∃y(=(x,ted) ∧ girl(y) ∧ meet(x,y) ∧ 
--    ∀z∀u((umbrella(z) ∧ =(u,y) ∧ of(z,u) ∧ forget(u,z)) → ¬∃v∃w(=(v,x) ∧ =(w,z) ∧ return(v,w))))
discourse4 = DRS [DRSRef "x",DRSRef "y"] [
            Rel (DRSRel "=") [DRSRef "x", DRSRef "ted"],
            Rel (DRSRel "girl") [DRSRef "y"],
            Rel (DRSRel "meet") [DRSRef "x", DRSRef "y"],
            Imp (DRS [DRSRef "z",DRSRef "u"] [Rel (DRSRel "umbrella") [DRSRef "z"], 
                                    Rel (DRSRel "=") [DRSRef "u",DRSRef "y"],
                                    Rel (DRSRel "of") [DRSRef "z",DRSRef "u"], 
                                    Rel (DRSRel "forget") [DRSRef "u",DRSRef "z"]]) 
                (DRS [] [Neg (DRS [DRSRef "v",DRSRef "w"] [Rel (DRSRel "=") [DRSRef "v",DRSRef "x"],
                                    Rel (DRSRel "=") [DRSRef "w",DRSRef "z"],
                                    Rel (DRSRel "return") [DRSRef "v",DRSRef "w"]])])]

-- Exercise 6.3

-- ted: ((e,t),t)
-- λg.∃z(=(z,ted) ∧ g(z))
ted :: (DRSRef -> DRS) -> DRS
ted g = Merge drs lambda
        where drs    = (DRS [DRSRef "z"] [Rel (DRSRel "=") [(DRSRef "z"), (DRSRef "ted")]])
              lambda = (g (DRSRef "z"))

-- sad: (e,t)
-- λx.sad(x)
sad :: DRSRef -> DRS
sad x = DRS [] [Rel (DRSRel "sad") [x]]

-- no: ((e,t),((e,t),t))
-- λp.λq.∀x(p(x) → ¬q(x))
no :: (DRSRef -> DRS) -> ((DRSRef -> DRS) -> DRS)
no p q = DRS [] [Imp antecedent consequent]
        where antecedent = Merge (DRS [(DRSRef "x")] []) (p (DRSRef "x"))
              consequent = DRS [] [Neg  (q (DRSRef "x"))]

-- no2: ((e,t),((e,t),t))
-- λp.λq.¬∃x(p(x) ∧ q(x))           
no2 :: (DRSRef -> DRS) -> ((DRSRef -> DRS) -> DRS)
no2 p q = DRS [] [Neg (Merge (Merge r_drs p_drs) q_drs)]
        where r_drs = DRS [DRSRef "x"] []
              p_drs = p (DRSRef "x")
              q_drs = q (DRSRef "x")

-- girl: (e,t)
-- λx.girl(x)
girl :: DRSRef -> DRS
girl x = DRS [] [Rel (DRSRel "girl") [x]]

-- because: (t,(t,t))
-- λd1.λd2.(d1 ∧ d2)
because :: DRS -> (DRS -> DRS)
because d1 d2 = Merge d1 d2

-- because2: (t,(t,t))
-- λd1.λd2.∃p1∃p2(p1:d1 ∧ p2:d2 ∧ because(p1,p2))
because2 :: DRS -> (DRS -> DRS)
because2 d1 d2 = DRS [p1,p2] [Prop p1 d1, Prop p2 d2, Rel (DRSRel "because") [p2,p1]]
      where p1 = DRSRef "p1"
            p2 = DRSRef "p2"

-- like: (e,(e,t))
-- λy.λx.like(x,y)
like :: DRSRef -> DRSRef -> DRS
like y x = DRS [] [Rel (DRSRel "like") [x, y]]

-- simplified pronoun resolution (see below)
-- him: e
-- z
him :: DRSRef
him = DRSRef "z"

-- these definitions follow the slides ...
-- him2: ((e,t),t)
-- λg.g(z)
him2 :: (DRSRef -> DRS) -> DRS
him2 g = g (DRSRef "z")

---------------------------------------
---------------------------------------

-- constituent derivations
ted_sad    = ted sad
no_girl    = no girl
no_girl2   = no2 girl
likes_him  = like him
likes_him2 = (\x -> him2 (flip like x))

-- simple derivation
deriv1 = because ted_sad (no_girl likes_him)
-- drsResolveMerges deriv1
-- drsToFOL $ drsResolveMerges deriv1

-- derivation using alternative definition of no
deriv2 = because ted_sad (no_girl2 likes_him)
-- drsResolveMerges deriv2
-- drsToFOL $ drsResolveMerges deriv2

-- derivation using alternative definition of because
deriv3 = because2 ted_sad (no_girl likes_him)
-- drsResolveMerges deriv3
-- drsToFOL $ drsResolveMerges deriv3

-- derivation using the pronoun definition in the slides
deriv4 = because ted_sad (no_girl likes_him2)
-- drsResolveMerges deriv4
-- drsToFOL $ drsResolveMerges deriv4
