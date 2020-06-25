import Data.DRS

-- Exercise 6.1

-- Either Michael Jordan plays basketball, or he plays baseball.
discourse1 = DRS [DRSRef "x"] [
            Rel (DRSRel "=") [DRSRef "x", DRSRef "MJ"],
            Or  (DRS [] [Rel (DRSRel "play_basketball") [DRSRef "x"]]) 
                (DRS [] [Rel (DRSRel "play_baseball") [DRSRef "x"]])]

-- Either Michael Jordan plays basketball, or he plays baseball.
discourse1b = DRS [DRSRef "x"] [
            Rel (DRSRel "=") [DRSRef "x", DRSRef "MJ"],
            Or  (DRS [] [Rel (DRSRel "play_basketball") [DRSRef "x"],
                        Neg (DRS [] [Rel (DRSRel "play_baseball") [DRSRef "x"]])]) 
                (DRS [] [Rel (DRSRel "play_baseball") [DRSRef "x"],
                        Neg (DRS [] [Rel (DRSRel "play_basketball") [DRSRef "x"]])])]

-- The Bulls do not win every match.
discourse2 = DRS [DRSRef "x"] [
            Rel (DRSRel "=") [DRSRef "x", DRSRef "Bulls"],
            Neg (DRS [] [Imp (DRS [DRSRef "y"] [Rel (DRSRel "match") [DRSRef "y"]]) 
                             (DRS [] [Rel (DRSRel "win") [DRSRef "x", DRSRef "y"]])])]

-- The Bulls do not win every match. (different DR availability!)
discourse2b = DRS [DRSRef "x",DRSRef "y"] [
                  Rel (DRSRel "=") [DRSRef "x", DRSRef "Bulls"],
                  Rel (DRSRel "match") [DRSRef "y"],
                  Neg (DRS [] [Rel (DRSRel "win") [DRSRef "x", DRSRef "y"]])]

-- If a player goes to a casino, he doesn’t come to practice.
discourse3 = DRS [] [
            Imp (DRS [DRSRef "x",DRSRef "y"] [
                                    Rel (DRSRel "player") [DRSRef "x"],
                                    Rel (DRSRel "casino") [DRSRef "y"], 
                                    Rel (DRSRel "go_to") [DRSRef "x",DRSRef "y"]]) 
                (DRS [] [Neg (DRS [DRSRef "v",DRSRef "w"] [
                                    Rel (DRSRel "=") [DRSRef "v",DRSRef "x"],
                                    Rel (DRSRel "practice") [DRSRef "w"],
                                    Rel (DRSRel "come_to") [DRSRef "v",DRSRef "w"]])])]

-- Exercise 6.2

-- mj: ((e,t),t)
-- λg.∃z(=(z,michael) ∧ g(z))
mj :: (DRSRef -> DRS) -> DRS
mj g = Merge drs lambda
        where drs    = (DRS [DRSRef "z"] [Rel (DRSRel "=") [(DRSRef "z"), (DRSRef "Michael")]])
              lambda = (g (DRSRef "z"))

-- happy: (e,t)
-- λx.happy(x)
happy :: DRSRef -> DRS
happy x = DRS [] [Rel (DRSRel "happy") [x]]

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

-- player: (e,t)
-- λx.player(x)
player :: DRSRef -> DRS
player x = DRS [] [Rel (DRSRel "player") [x]]

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

-- beat: (e,(e,t))
-- λy.λx.beat(x,y)
beat :: DRSRef -> DRSRef -> DRS
beat y x = DRS [] [Rel (DRSRel "beat") [x, y]]

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

-- simple derivation
deriv1 = because (mj happy) ((no player) (beat him))
-- drsResolveMerges deriv1
-- drsToFOL $ drsResolveMerges deriv1

-- derivation using alternative definition of no
deriv2 = because (mj happy) ((no2 player) (beat him))
-- drsResolveMerges deriv2
-- drsToFOL $ drsResolveMerges deriv2

-- derivation using alternative definition of because
deriv3 = because2 (mj happy) ((no player) (beat him))
-- drsResolveMerges deriv3
-- drsToFOL $ drsResolveMerges deriv3

-- derivation using the pronoun definition in the slides
deriv4 = because (mj happy) ((no player) (\x -> him2 (flip beat x)))
-- drsResolveMerges deriv4
-- drsToFOL $ drsResolveMerges deriv4
