---- MODULE MC ----
EXTENDS Wallet, TLC

\* CONSTANT definitions @modelParameterConstants:0TOKENS
const_1677778601870171000 == 
{"t1", "t2"}
----

\* CONSTANT definitions @modelParameterConstants:1ADDRESSES
const_1677778601872172000 == 
{"a1", "a2", "r1"}
----

\* CONSTANT definitions @modelParameterConstants:2TOKEN_MAPPING
const_1677778601872173000 == 
[a1 |-> {"t1", "t2"}, a2 |-> {}, r1 |-> {}]
----

\* CONSTANT definitions @modelParameterConstants:3WEBSITES
const_1677778601872174000 == 
{"w1", "w2"}
----

\* CONSTANT definitions @modelParameterConstants:4MAX_SIGNATURES
const_1677778601872175000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:5WEBSITE_MAPPING
const_1677778601872176000 == 
[t1 |-> {"w1"}, t2 |-> {"w1", "w2"}]
----

\* CONSTANT definitions @modelParameterConstants:6MAX_RELAYS
const_1677778601872177000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:7RELAYER_MAPPING
const_1677778601872178000 == 
[t1 |-> {"r1"}, t2 |-> {}]
----

=============================================================================
