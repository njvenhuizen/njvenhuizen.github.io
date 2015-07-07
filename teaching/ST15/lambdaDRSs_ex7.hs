import Data.DRS

everystudent k0 = DRS [] [Imp 
                        (DRS [DRSRef "z"][Rel (DRSRel "student") [DRSRef "z"]]) 
                        (k0 (DRSRef "z"))]

works x         = DRS [] [Rel (DRSRel "work") [x]]

astudent k0     = (DRS [DRSRef "z"][Rel (DRSRel "student") [DRSRef "z"]]) 
                  <<+>> (k0 (DRSRef "z"))

mary k0         = (DRS [DRSRef "z"][
                    Rel (DRSRel "=") [DRSRef "z",DRSRef "Mary"]])
                  <<+>> (k0 (DRSRef "z"))

she k0          = k0 (DRSRef "z")

issuccessful x  = DRS [] [Rel (DRSRel "successful") [x]]

---

like x y        = DRS [] [Rel (DRSRel "like") [y,x]]

no1 k0 k1       = DRS [] [Imp 
                            ((DRS [DRSRef "x"] []) <<+>> (k0 (DRSRef "x"))) 
                            (DRS [] [Neg (k1 (DRSRef "x"))])]

no2 k0 k1       = DRS [] [Neg 
                            ((DRS [DRSRef "x"] []) 
                            <<+>> (k0 (DRSRef "x")) 
                            <<+>> (k1 (DRSRef "x")))]

because1 k0 k1  = k0 <<+>> k1

because2 k0 k1  = DRS [DRSRef "p1", DRSRef "p2"] [
                    Prop (DRSRef "p1") k0, 
                    Prop (DRSRef "p2") k1, 
                    Rel (DRSRel "because") [DRSRef "p2", DRSRef "p1"]] 

girl x          = DRS [] [Rel (DRSRel "girl") [x]]

ted k0          = (DRS [DRSRef "z"][Rel (DRSRel "ted=") [DRSRef "z"]]) 
                  <<+>> (k0 (DRSRef "z"))

sad x           = DRS [] [Rel (DRSRel "sad") [x]]

him             = (DRSRef "z")

