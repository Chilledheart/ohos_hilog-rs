extern crate ohos_hilog;
extern crate log;

#[test]
fn default_init() {
    ohos_hilog::init_once(Default::default());

    // ohos_hilog has default log level "off"
    assert_eq!(log::max_level(), log::LevelFilter::Off);
}
