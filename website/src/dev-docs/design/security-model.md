# Security Model

Blockchain client security is the problem of preventing fraudulent transactions
with users' keys. A fraudulent transaction is a blockchain transaction carried
out or instigated by a third party that the user did not intend to carry out or
intended to carry out with different parameters. Fraudulent transactions can
occur through technical means or deception or through a combination of these.

## Deception-Mitigation

!!! quote ""
    Only amateurs attack machines; professionals target people. --
    [Bruce Schneier](https://www.schneier.com/crypto-gram/archives/2000/1015.html#1)

Phishing and social engineering attacks (deception attacks) rely on a mistaken
belief by the user either on the premises or the consequences of their actions.

Our primary strategy to deal with deception attacks is to eliminate attack
vectors. If the user can't perform a certain action, it's no longer possible to
target that action in a deception attack.

Our secondary strategy to deal with deception attacks is to limit their scope.
This reduces damage to individual users who have fallen prey to an attack and
protects the collective by reducing incentives for deception attacks.

Our tertiary strategy to deal with deception attacks is to highlight possible
false premises if we can detect them. For example, we can warn users that a
transaction hasn't been verified locally, that the contract address(es) have
changed for a dapp or that they're about to spend a much higher amount than they usually do.


