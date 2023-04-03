---- MODULE MCWallet ----
EXTENDS Wallet, TLC

MC_TOKEN_MAPPING == [a1 |-> {"t1", "t2"}, a2 |-> {}, r1 |-> {}]
MC_RELAYER_MAPPING == [t1 |-> {"r1"}, t2 |-> {}]
MC_WEBSITE_MAPPING == [t1 |-> {"w1"}, t2 |-> {"w1", "w2"}]

====
