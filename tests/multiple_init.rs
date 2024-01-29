extern crate ohos_hilog;
extern crate log;

#[test]
fn multiple_init() {
    ohos_hilog::init_once(
        ohos_hilog::Config::default().with_max_level(log::LevelFilter::Trace),
    );

    // Second initialization should be silently ignored
    ohos_hilog::init_once(
        ohos_hilog::Config::default().with_max_level(log::LevelFilter::Error),
    );

    assert_eq!(log::max_level(), log::LevelFilter::Trace);
}
