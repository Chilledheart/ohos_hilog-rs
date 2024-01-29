extern crate ohos_hilog;
extern crate log;

#[test]
fn config_log_level() {
    ohos_hilog::init_once(
        ohos_hilog::Config::default().with_max_level(log::LevelFilter::Trace),
    );

    assert_eq!(log::max_level(), log::LevelFilter::Trace);
}
