---
id: 01M5TXKQ7DK24ZGSW68RQZXJGB
anchor: ThrowawayKeychain
created: 2026-10-26T01:36:14Z
norm: '1'
---

Keychain calls are serialized: a read racing the app's forgetSecret deadlocked inside Security's file keychain (cairn#237)
