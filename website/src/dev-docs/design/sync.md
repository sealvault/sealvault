# Sync (WIP)

Syncing data between a user's devices is planned for future releases.

## Deterministic Ids

We use deterministic ids as primary keys for synced database entities,
because deterministic ids make it easier to maintain referential integrity when
syncing.

The deterministic id is derived by producing a
[BLAKE3](https://github.com/BLAKE3-team/BLAKE3) hash of the namespaced entity
name and the unique fields of the entity with a 256-bit tag. The deterministic
id is used as a basis for security-decisions, so it's critical that adversaries
cannot create collisions.

The 256-bit tag is an extremely conservative parameter, because syncing is done
among one user's devices, and we can assume with a large margin of error that no
user will have more than $2^{24}$ items in a synced table since these items
are typically created on first user interaction with a dapp. This means that
there is an approx. $2^{-209}$ probability of collision for ids in each
table, which is negligible with an extremely large margin of error, and is safe
even against adversaries with unexpected quantum-computing capabilities. On the
other hand, picking a shorter tag wouldn't bring any real benefits, as by
halving the tag size, we could save a few megabytes of storage for power users,
and it wouldn't speed up DB queries in any meaningful way.

Due to our usage of deterministic ids, we treat unique columns as immutable,
i.e. if a unique column needs to be changed, a new entity is created. DB
entities that have deterministic ids may only have a single unique constraint on
the table other than the primary key. This unique constraint may not span
nullable columns, as null values are treated as not-equal by SQL which goes
against the purpose of deterministic ids.

When receiving an empty value for one of the unique values, the deterministic id
implementation hashes a special marker value in place of the empty value in
order to distinguish between `["", "foo"]`  and `["foo", ""]` and between unique
values of differing lengths (the latter could be handled by including the length
in the hash as well). The marker value is a random 256-bit value hard-coded into
the implementation. The implementation returns an error if it receives the
marker value as one of the unique values in order to prevent adversarial attacks
simulating an empty value.

The tag bytes are stored as a base32-encoded (no padding) string in the DB to
help with debugging.
