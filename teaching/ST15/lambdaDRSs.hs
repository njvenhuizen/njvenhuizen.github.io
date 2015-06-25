import Data.DRS


works x         = DRS [] [Rel (DRSRel "work") [x]]

everystudent k0 = DRS [] [Imp (DRS [DRSRef "z"][Rel (DRSRel "student") [DRSRef "z"]]) (k0 (DRSRef "z"))]

astudent k0     = (DRS [DRSRef "z"][Rel (DRSRel "student") [DRSRef "z"]]) <<+>> (k0 (DRSRef "z"))

mary k0         = (DRS [DRSRef "z"][Rel (DRSRel "=") [DRSRef "z",DRSRef "Mary"]]) <<+>> (k0 (DRSRef "z"))

she k0          = k0 (DRSRef "z")

astudentworks   = DRS [DRSRef "z"][Rel (DRSRel "student") [DRSRef "z"], Rel (DRSRel "work") [DRSRef "z"]]

sheissuccessful = DRS [] [Rel (DRSRel "successful") [DRSRef "z"]]
