import Data.DRS

-- | to_like: λxλy.like(y,x) :: <e,<et>>
like1 x y       = DRS [] [Rel (DRSRel "like") [y,x]]

-- | to_like (type-raised): λpλy.p(λx(like(y,x))) :: < <<et>,t>,<et>>
like2 p y       = p (\x -> (DRS [] [Rel (DRSRel "like") [y,x]]))

-- | no: λPλQ.∀x(P(x) -> ¬Q(x) :: <<et>,<<et>,t>>
no1 k0 k1       = DRS [] [Imp 
                            ((DRS [DRSRef "x"] []) <<+>> (k0 (DRSRef "x"))) 
                            (DRS [] [Neg (k1 (DRSRef "x"))])]

-- | no: λPλQ.¬Ǝx(P(x) ∧ Q(x) :: <<et>,<<et>,t>>
no2 k0 k1       = DRS [] [Neg 
                            ((DRS [DRSRef "x"] []) 
                            <<+>> (k0 (DRSRef "x")) 
                            <<+>> (k1 (DRSRef "x")))]

-- | because: λSλT.S ∧ T :: <t,<tt>>
because1 k0 k1  = k0 <<+>> k1

-- | because: λSλT.(S -> T) ∧ S ∧ T :: <t,<tt>>
because2 k0 k1  = DRS [] [Imp k0 k1] <<+>> k0 <<+>> k1

-- | because: λSλT.ƎpƎq(p:S ∧ q:T ∧ because(p,q)) :: <t,<tt>>
because3 k0 k1  = DRS [DRSRef "p1", DRSRef "p2"] [
                    Prop (DRSRef "p1") k0, 
                    Prop (DRSRef "p2") k1, 
                    Rel (DRSRel "because") [DRSRef "p1", DRSRef "p2"]] 

-- | girl: λx.girl(x) :: <et>
girl x          = DRS [] [Rel (DRSRel "girl") [x]]

-- | ted (generalized quantifier): λP.Ǝz(ted=z ∧ P(z)) :: <<et>,t>
ted k0          = (DRS [DRSRef "z"][Rel (DRSRel "ted=") [DRSRef "z"]]) 
                  <<+>> (k0 (DRSRef "z"))

-- | sad: λx.sad(x) :: <et>
sad x           = DRS [] [Rel (DRSRel "sad") [x]]

-- | him: z :: e
him             = (DRSRef "z")



sentence =  because3 (no2 girl (like2 ted)) (ted sad)


sentence2 = (\p -> because3 (no2 girl (like2 p)) (p sad)) ted

sentence3 = ted (\x -> because3 (no2 girl (like1 x)) (sad x))
