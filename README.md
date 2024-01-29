## Send Rust logs to Logcat

[![Version](https://img.shields.io/crates/v/ohos_hilog.svg)](https://crates.io/crates/ohos_hilog)

This library is a drop-in replacement for `env_logger`. Instead, it outputs messages to
ohos's logcat.

This only works on Open Harmony and requires linking to `hilog.z` which
is only available under open harmony. With Cargo, it is possible to conditionally require
this library:

```toml
[target.'cfg(all(target_os = "linux", target_env = "ohos"))'.dependencies]
ohos_hilog = "0.1"
```

Example of initialization on activity creation, with log configuration:

```rust
#[macro_use] extern crate log;
extern crate ohos_hilog;

use log::LevelFilter;
use ohos_hilog::{Config,FilterBuilder};

fn native_activity_create() {
    ohos_hilog::init_once(
        Config::default()
            .with_max_level(LevelFilter::Trace) // limit log level
            .with_tag("mytag") // logs will show under mytag tag
            .with_filter( // configure messages for specific crate
                FilterBuilder::new()
                    .parse("debug,hello::crate=error")
                    .build())
    );

    trace!("this is a verbose {}", "message");
    error!("this is printed by default");
}
```

To allow all logs, use the default configuration with min level Trace:

```rust
#[macro_use] extern crate log;
extern crate ohos_hilog;

use log::LevelFilter;
use ohos_hilog::Config;

fn native_activity_create() {
    ohos_hilog::init_once(
        Config::default().with_max_level(LevelFilter::Trace),
    );
}
```

There is a caveat that this library can only be initialized once
(hence the `init_once` function name).
Therefore this library will only log a warning for subsequent `init_once` calls.

This library ensures that logged messages do not overflow open harmony hilog log message limits
by efficiently splitting messages into chunks.

## License

Licensed under either of

 * Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally
submitted for inclusion in the work by you, as defined in the Apache-2.0
license, shall be dual licensed as above, without any additional terms or
conditions.
