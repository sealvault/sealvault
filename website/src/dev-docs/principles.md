# Principles

Our introductory blog [post](https://sealvault.org/blog/web3-vision) describes
why we're building SealVault. These principles serve as general guidelines to
daily decisions:

1. The purpose of this project is to serve users. Every decision should be
   **anchored to a user need.**
1. **Users own their keys.** Ownership of keys means that users have exclusive
   control over the keys, including switching key management applications.[^1]
1. Don't preach.  We don't try to make users change their behavior.  Instead, we
   build solutions that fit into users' usage patterns and mental models. **If
   the user fucks up, that means we fucked up.**
1. UX is an optimizing metric, privacy and security are satisficing metrics.  We
   guarantee well-defined [security](./design/security-model.md) and
   [privacy](./design/privacy-model.md) models for users, but beyond those we
   always **optimize for UX.**
1. **Support available methods.**  We make use of platform or user specific
   tools that provide value to users whenever possible.
1. **Platform-specific UI design.**  Use familiar UI elements and iconography.
1. **Forkable.**  It should be possible to take the code base and build
   something new with it.  This keeps us honest and promotes innovation which we
   can channel back to the app thanks to our copyleft license.[^2]

[^1]: 
It's non-trivial to make secrets exportable in a secure and user-friendly way
and the design is still WIP. Get involved on the
[forum](https://forum.sealvault.org) to help design this feature!

[^2]:
Note that not all open source licenses make a project forkable. For
example, under a GPL license one can fork the code but then can't publish it in
the iOS App Store since the source code can't be provided through the App Store
which is required by the GPL. We chose MPL 2.0 over GPL for this reason.


