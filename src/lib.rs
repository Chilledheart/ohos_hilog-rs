// Copyright 2024 The ohos_hilog Developers
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

//! A logger which writes to ohos output.
//!
//! ## Example
//!
//! ```
//! #[macro_use] extern crate log;
//! extern crate ohos_hilog;
//!
//! use log::LevelFilter;
//! use ohos_hilog::Config;
//!
//! /// Ohos code may not have obvious "main", this is just an example.
//! fn main() {
//!     ohos_hilog::init_once(
//!         Config::default().with_max_level(LevelFilter::Trace),
//!     );
//!
//!     debug!("this is a debug {}", "message");
//!     error!("this is printed by default");
//! }
//! ```
//!
//! ## Example with module path filter
//!
//! It is possible to limit log messages to output from a specific crate,
//! and override the logcat tag name (by default, the crate name is used):
//!
//! ```
//! #[macro_use] extern crate log;
//! extern crate ohos_hilog;
//!
//! use log::LevelFilter;
//! use ohos_hilog::{Config,FilterBuilder};
//!
//! fn main() {
//!     ohos_hilog::init_once(
//!         Config::default()
//!             .with_max_level(LevelFilter::Trace)
//!             .with_tag("mytag")
//!             .with_filter(FilterBuilder::new().parse("debug,hello::crate=trace").build()),
//!     );
//!
//!     // ..
//! }
//! ```
//!
//! ## Example with a custom log formatter
//!
//! ```
//! use ohos_hilog::Config;
//!
//! ohos_hilog::init_once(
//!     Config::default()
//!         .with_max_level(log::LevelFilter::Trace)
//!         .format(|f, record| write!(f, "my_app: {}", record.args()))
//! )
//! ```

#[cfg(all(target_os = "linux", target_env = "ohos"))]
extern crate ohos_hilog_sys as log_ffi;
extern crate once_cell;
use once_cell::sync::OnceCell;
#[macro_use]
extern crate log;

extern crate env_logger;

use log::{Level, LevelFilter, Log, Metadata, Record};
#[cfg(all(target_os = "linux", target_env = "ohos"))]
use log_ffi::LogType;
#[cfg(all(target_os = "linux", target_env = "ohos"))]
use log_ffi::LogLevel;
use std::ffi::{CStr, CString};
use std::fmt;
use std::mem::{self, MaybeUninit};
use std::ptr;

pub use env_logger::filter::{Builder as FilterBuilder, Filter};
pub use env_logger::fmt::Formatter;

pub(crate) type FormatFn = Box<dyn Fn(&mut dyn fmt::Write, &Record) -> fmt::Result + Sync + Send>;

/// Outputs log to Ohos system.
#[cfg(all(target_os = "linux", target_env = "ohos"))]
fn ohos_log(
    buf_id: Option<LogType>,
    level: LogLevel,
    tag: &CStr,
    msg: &CStr,
) {
    if let Some(buf_id) = buf_id {
        unsafe {
            log_ffi::OH_LOG_Print(
                buf_id as LogType,
                level,
                0 as log_ffi::c_uint,
                tag.as_ptr() as *const log_ffi::c_char,
                msg.as_ptr() as *const log_ffi::c_char,
            );
        };
    } else {
        unsafe {
            log_ffi::OH_LOG_Print(
                log_ffi::LogType::LOG_APP,
                level,
                0 as log_ffi::c_uint,
                tag.as_ptr() as *const log_ffi::c_char,
                msg.as_ptr() as *const log_ffi::c_char,
            );
        };
    }
}

/// Dummy output placeholder for tests.
#[cfg(not(all(target_os = "linux", target_env = "ohos")))]
fn ohos_log(_buf_id: Option<u32>, _level: Level, _tag: &CStr, _msg: &CStr) {}

/// Underlying ohos logger backend
pub struct OhosLogger {
    config: OnceCell<Config>,
}

impl OhosLogger {
    /// Create new logger instance from config
    pub fn new(config: Config) -> OhosLogger {
        OhosLogger {
            config: OnceCell::from(config),
        }
    }

    fn config(&self) -> &Config {
        self.config.get_or_init(Config::default)
    }
}

static OHOS_LOGGER: OnceCell<OhosLogger> = OnceCell::new();

const LOGGING_TAG_MAX_LEN: usize = 23;
const LOGGING_MSG_MAX_LEN: usize = 4000;

impl Default for OhosLogger {
    /// Create a new logger with default config
    fn default() -> OhosLogger {
        OhosLogger {
            config: OnceCell::from(Config::default()),
        }
    }
}

impl Log for OhosLogger {
    fn enabled(&self, metadata: &Metadata) -> bool {
        let config = self.config();
        // todo: consider OH_LOG_IsLoggable.
        metadata.level() <= config.log_level.unwrap_or_else(log::max_level)
    }

    fn log(&self, record: &Record) {
        let config = self.config();

        if !self.enabled(record.metadata()) {
            return;
        }

        // this also checks the level, but only if a filter was
        // installed.
        if !config.filter_matches(record) {
            return;
        }

        // tag must not exceed LOGGING_TAG_MAX_LEN
        let mut tag_bytes: [MaybeUninit<u8>; LOGGING_TAG_MAX_LEN + 1] = uninit_array();

        let module_path = record.module_path().unwrap_or_default().to_owned();

        // If no tag was specified, use module name
        let custom_tag = &config.tag;
        let tag = custom_tag
            .as_ref()
            .map(|s| s.as_bytes())
            .unwrap_or_else(|| module_path.as_bytes());

        // truncate the tag here to fit into LOGGING_TAG_MAX_LEN
        self.fill_tag_bytes(&mut tag_bytes, tag);
        // use stack array as C string
        let tag: &CStr = unsafe { CStr::from_ptr(mem::transmute(tag_bytes.as_ptr())) };

        // message must not exceed LOGGING_MSG_MAX_LEN
        // therefore split log message into multiple log calls
        let mut writer = PlatformLogWriter::new(config.buf_id, record.level(), tag);

        // If a custom tag is used, add the module path to the message.
        // Use PlatformLogWriter to output chunks if they exceed max size.
        let _ = match (custom_tag, &config.custom_format) {
            (_, Some(format)) => format(&mut writer, record),
            (Some(_), _) => fmt::write(
                &mut writer,
                format_args!("{}: {}", module_path, *record.args()),
            ),
            _ => fmt::write(&mut writer, *record.args()),
        };

        // output the remaining message (this would usually be the most common case)
        writer.flush();
    }

    fn flush(&self) {}
}

impl OhosLogger {
    fn fill_tag_bytes(&self, array: &mut [MaybeUninit<u8>], tag: &[u8]) {
        if tag.len() > LOGGING_TAG_MAX_LEN {
            for (input, output) in tag
                .iter()
                .take(LOGGING_TAG_MAX_LEN - 2)
                .chain(b"..\0".iter())
                .zip(array.iter_mut())
            {
                output.write(*input);
            }
        } else {
            for (input, output) in tag.iter().chain(b"\0".iter()).zip(array.iter_mut()) {
                output.write(*input);
            }
        }
    }
}

/// Filter for ohos logger.
#[derive(Default)]
pub struct Config {
    log_level: Option<LevelFilter>,
    #[cfg(all(target_os = "linux", target_env = "ohos"))]
    buf_id: Option<LogType>,
    #[cfg(not(all(target_os = "linux", target_env = "ohos")))]
    buf_id: Option<u32>,
    filter: Option<env_logger::filter::Filter>,
    tag: Option<CString>,
    custom_format: Option<FormatFn>,
}

impl Config {
    /// Changes the maximum log level.
    ///
    /// Note, that `Trace` is the maximum level, because it provides the
    /// maximum amount of detail in the emitted logs.
    ///
    /// If `Off` level is provided, then nothing is logged at all.
    ///
    /// [`log::max_level()`] is considered as the default level.
    pub fn with_max_level(mut self, level: LevelFilter) -> Self {
        self.log_level = Some(level);
        self
    }

    /// Changes the Ohos logging system buffer to be used.
    ///
    /// By default, logs are sent to the [`Main`] log. Other logging buffers may
    /// only be accessible to certain processes.
    ///
    /// [`Main`]: LogType::LOG_APP
    #[cfg(all(target_os = "linux", target_env = "ohos"))]
    pub fn with_log_buffer(mut self, buf_id: LogType) -> Self {
        self.buf_id = Some(buf_id);
        self
    }
    #[cfg(not(all(target_os = "linux", target_env = "ohos")))]
    pub fn with_log_buffer(mut self, buf_id: u32) -> Self {
        self.buf_id = Some(buf_id);
        self
    }

    fn filter_matches(&self, record: &Record) -> bool {
        if let Some(ref filter) = self.filter {
            filter.matches(record)
        } else {
            true
        }
    }

    pub fn with_filter(mut self, filter: env_logger::filter::Filter) -> Self {
        self.filter = Some(filter);
        self
    }

    pub fn with_tag<S: Into<Vec<u8>>>(mut self, tag: S) -> Self {
        self.tag = Some(CString::new(tag).expect("Can't convert tag to CString"));
        self
    }

    /// Sets the format function for formatting the log output.
    /// ```
    /// # use ohos_hilog::Config;
    /// ohos_hilog::init_once(
    ///     Config::default()
    ///         .with_max_level(log::LevelFilter::Trace)
    ///         .format(|f, record| write!(f, "my_app: {}", record.args()))
    /// )
    /// ```
    pub fn format<F>(mut self, format: F) -> Self
    where
        F: Fn(&mut dyn fmt::Write, &Record) -> fmt::Result + Sync + Send + 'static,
    {
        self.custom_format = Some(Box::new(format));
        self
    }
}

pub struct PlatformLogWriter<'a> {
    #[cfg(all(target_os = "linux", target_env = "ohos"))]
    level: LogLevel,
    #[cfg(not(all(target_os = "linux", target_env = "ohos")))]
    level: Level,
    #[cfg(all(target_os = "linux", target_env = "ohos"))]
    buf_id: Option<LogType>,
    #[cfg(not(all(target_os = "linux", target_env = "ohos")))]
    buf_id: Option<u32>,
    len: usize,
    last_newline_index: usize,
    tag: &'a CStr,
    buffer: [MaybeUninit<u8>; LOGGING_MSG_MAX_LEN + 1],
}

impl<'a> PlatformLogWriter<'a> {
    #[cfg(all(target_os = "linux", target_env = "ohos"))]
    pub fn new_with_level(
        buf_id: Option<LogType>,
        level: LogLevel,
        tag: &CStr,
    ) -> PlatformLogWriter<'_> {
        #[allow(deprecated)] // created an issue #35 for this
        PlatformLogWriter {
            level,
            buf_id: buf_id,
            len: 0,
            last_newline_index: 0,
            tag,
            buffer: uninit_array(),
        }
    }

    #[cfg(all(target_os = "linux", target_env = "ohos"))]
    pub fn new(buf_id: Option<LogType>, level: Level, tag: &CStr) -> PlatformLogWriter<'_> {
        PlatformLogWriter::new_with_level(
            buf_id,
            match level {
                Level::Warn => LogLevel::WARN,
                Level::Info => LogLevel::INFO,
                Level::Debug => LogLevel::DEBUG,
                Level::Error => LogLevel::ERROR,
                Level::Trace => LogLevel::DEBUG,
            },
            tag,
        )
    }

    #[cfg(not(all(target_os = "linux", target_env = "ohos")))]
    pub fn new(buf_id: Option<u32>, level: Level, tag: &CStr) -> PlatformLogWriter<'_> {
        #[allow(deprecated)] // created an issue #35 for this
        PlatformLogWriter {
            level: level,
            buf_id,
            len: 0,
            last_newline_index: 0,
            tag,
            buffer: uninit_array(),
        }
    }

    /// Flush some bytes to ohos logger.
    ///
    /// If there is a newline, flush up to it.
    /// If ther was no newline, flush all.
    ///
    /// Not guaranteed to flush everything.
    fn temporal_flush(&mut self) {
        let total_len = self.len;

        if total_len == 0 {
            return;
        }

        if self.last_newline_index > 0 {
            let copy_from_index = self.last_newline_index;
            let remaining_chunk_len = total_len - copy_from_index;

            self.output_specified_len(copy_from_index);
            self.copy_bytes_to_start(copy_from_index, remaining_chunk_len);
            self.len = remaining_chunk_len;
        } else {
            self.output_specified_len(total_len);
            self.len = 0;
        }
        self.last_newline_index = 0;
    }

    /// Flush everything remaining to ohos logger.
    pub fn flush(&mut self) {
        let total_len = self.len;

        if total_len == 0 {
            return;
        }

        self.output_specified_len(total_len);
        self.len = 0;
        self.last_newline_index = 0;
    }

    /// Output buffer up until the \0 which will be placed at `len` position.
    fn output_specified_len(&mut self, len: usize) {
        let mut last_byte = MaybeUninit::new(b'\0');

        mem::swap(&mut last_byte, unsafe {
            self.buffer.get_unchecked_mut(len)
        });

        let msg: &CStr = unsafe { CStr::from_ptr(self.buffer.as_ptr().cast()) };
        ohos_log(self.buf_id, self.level, self.tag, msg);

        unsafe { *self.buffer.get_unchecked_mut(len) = last_byte };
    }

    /// Copy `len` bytes from `index` position to starting position.
    fn copy_bytes_to_start(&mut self, index: usize, len: usize) {
        let dst = self.buffer.as_mut_ptr();
        let src = unsafe { self.buffer.as_ptr().add(index) };
        unsafe { ptr::copy(src, dst, len) };
    }
}

impl<'a> fmt::Write for PlatformLogWriter<'a> {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        let mut incomming_bytes = s.as_bytes();

        while !incomming_bytes.is_empty() {
            let len = self.len;

            // write everything possible to buffer and mark last \n
            let new_len = len + incomming_bytes.len();
            let last_newline = self.buffer[len..LOGGING_MSG_MAX_LEN]
                .iter_mut()
                .zip(incomming_bytes)
                .enumerate()
                .fold(None, |acc, (i, (output, input))| {
                    output.write(*input);
                    if *input == b'\n' {
                        Some(i)
                    } else {
                        acc
                    }
                });

            // update last \n index
            if let Some(newline) = last_newline {
                self.last_newline_index = len + newline;
            }

            // calculate how many bytes were written
            let written_len = if new_len <= LOGGING_MSG_MAX_LEN {
                // if the len was not exceeded
                self.len = new_len;
                new_len - len // written len
            } else {
                // if new length was exceeded
                self.len = LOGGING_MSG_MAX_LEN;
                self.temporal_flush();

                LOGGING_MSG_MAX_LEN - len // written len
            };

            incomming_bytes = &incomming_bytes[written_len..];
        }

        Ok(())
    }
}

/// Send a log record to Ohos logging backend.
///
/// This action does not require initialization. However, without initialization it
/// will use the default filter, which allows all logs.
pub fn log(record: &Record) {
    OHOS_LOGGER
        .get_or_init(OhosLogger::default)
        .log(record)
}

/// Initializes the global logger with an ohos logger.
///
/// This can be called many times, but will only initialize logging once,
/// and will not replace any other previously initialized logger.
///
/// It is ok to call this at the activity creation, and it will be
/// repeatedly called on every lifecycle restart (i.e. screen rotation).
pub fn init_once(config: Config) {
    let log_level = config.log_level;
    let logger = OHOS_LOGGER.get_or_init(|| OhosLogger::new(config));

    if let Err(err) = log::set_logger(logger) {
        debug!("ohos_hilog: log::set_logger failed: {}", err);
    } else if let Some(level) = log_level {
        log::set_max_level(level);
    }
}

// FIXME: When `maybe_uninit_uninit_array ` is stabilized, use it instead of this helper
fn uninit_array<const N: usize, T>() -> [MaybeUninit<T>; N] {
    // SAFETY: Array contains MaybeUninit, which is fine to be uninit
    unsafe { MaybeUninit::uninit().assume_init() }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fmt::Write;
    use std::sync::atomic::{AtomicBool, Ordering};

    #[test]
    fn check_config_values() {
        // Filter is checked in config_filter_match below.
        let config = Config::default()
            .with_max_level(LevelFilter::Trace)
            .with_log_buffer(0)
            .with_tag("my_app");

        assert_eq!(config.log_level, Some(LevelFilter::Trace));
        assert_eq!(config.buf_id, Some(0));
        assert_eq!(config.tag, Some(CString::new("my_app").unwrap()));
    }

    #[test]
    fn log_calls_formatter() {
        static FORMAT_FN_WAS_CALLED: AtomicBool = AtomicBool::new(false);
        let config = Config::default()
            .with_max_level(LevelFilter::Info)
            .format(|_, _| {
                FORMAT_FN_WAS_CALLED.store(true, Ordering::SeqCst);
                Ok(())
            });
        let logger = OhosLogger::new(config);

        logger.log(&Record::builder().level(Level::Info).build());

        assert!(FORMAT_FN_WAS_CALLED.load(Ordering::SeqCst));
    }

    #[test]
    fn logger_enabled_threshold() {
        let logger = OhosLogger::new(Config::default().with_max_level(LevelFilter::Info));

        assert!(logger.enabled(&log::MetadataBuilder::new().level(Level::Warn).build()));
        assert!(logger.enabled(&log::MetadataBuilder::new().level(Level::Info).build()));
        assert!(!logger.enabled(&log::MetadataBuilder::new().level(Level::Debug).build()));
    }

    // Test whether the filter gets called correctly. Not meant to be exhaustive for all filter
    // options, as these are handled directly by the filter itself.
    #[test]
    fn config_filter_match() {
        let info_record = Record::builder().level(Level::Info).build();
        let debug_record = Record::builder().level(Level::Debug).build();

        let info_all_filter = env_logger::filter::Builder::new().parse("info").build();
        let info_all_config = Config::default().with_filter(info_all_filter);

        assert!(info_all_config.filter_matches(&info_record));
        assert!(!info_all_config.filter_matches(&debug_record));
    }

    #[test]
    fn fill_tag_bytes_truncates_long_tag() {
        let logger = OhosLogger::new(Config::default());
        let too_long_tag: [u8; LOGGING_TAG_MAX_LEN + 20] = [b'a'; LOGGING_TAG_MAX_LEN + 20];

        let mut result: [MaybeUninit<u8>; LOGGING_TAG_MAX_LEN + 1] = uninit_array();
        logger.fill_tag_bytes(&mut result, &too_long_tag);

        let mut expected_result = [b'a'; LOGGING_TAG_MAX_LEN - 2].to_vec();
        expected_result.extend("..\0".as_bytes());
        assert_eq!(unsafe { assume_init_slice(&result) }, expected_result);
    }

    #[test]
    fn fill_tag_bytes_keeps_short_tag() {
        let logger = OhosLogger::new(Config::default());
        let short_tag: [u8; 3] = [b'a'; 3];

        let mut result: [MaybeUninit<u8>; LOGGING_TAG_MAX_LEN + 1] = uninit_array();
        logger.fill_tag_bytes(&mut result, &short_tag);

        let mut expected_result = short_tag.to_vec();
        expected_result.push(0);
        assert_eq!(unsafe { assume_init_slice(&result[..4]) }, expected_result);
    }

    #[test]
    fn platform_log_writer_init_values() {
        let tag = CStr::from_bytes_with_nul(b"tag\0").unwrap();

        let writer = PlatformLogWriter::new(None, Level::Warn, tag);

        assert_eq!(writer.tag, tag);
        // Ohos uses LogLevel instead, which doesn't implement equality checks
        #[cfg(not(all(target_os = "linux", target_env = "ohos")))]
        assert_eq!(writer.level, Level::Warn);
    }

    #[test]
    fn temporal_flush() {
        let mut writer = get_tag_writer();

        writer
            .write_str("12\n\n567\n90")
            .expect("Unable to write to PlatformLogWriter");

        assert_eq!(writer.len, 10);
        writer.temporal_flush();
        // Should have flushed up until the last newline.
        assert_eq!(writer.len, 3);
        assert_eq!(writer.last_newline_index, 0);
        assert_eq!(
            unsafe { assume_init_slice(&writer.buffer[..writer.len]) },
            "\n90".as_bytes()
        );

        writer.temporal_flush();
        // Should have flushed all remaining bytes.
        assert_eq!(writer.len, 0);
        assert_eq!(writer.last_newline_index, 0);
    }

    #[test]
    fn flush() {
        let mut writer = get_tag_writer();
        writer
            .write_str("abcdefghij\n\nklm\nnopqr\nstuvwxyz")
            .expect("Unable to write to PlatformLogWriter");

        writer.flush();

        assert_eq!(writer.last_newline_index, 0);
        assert_eq!(writer.len, 0);
    }

    #[test]
    fn last_newline_index() {
        let mut writer = get_tag_writer();

        writer
            .write_str("12\n\n567\n90")
            .expect("Unable to write to PlatformLogWriter");

        assert_eq!(writer.last_newline_index, 7);
    }

    #[test]
    fn output_specified_len_leaves_buffer_unchanged() {
        let mut writer = get_tag_writer();
        let log_string = "abcdefghij\n\nklm\nnopqr\nstuvwxyz";
        writer
            .write_str(log_string)
            .expect("Unable to write to PlatformLogWriter");

        writer.output_specified_len(5);

        assert_eq!(
            unsafe { assume_init_slice(&writer.buffer[..log_string.len()]) },
            log_string.as_bytes()
        );
    }

    #[test]
    fn copy_bytes_to_start() {
        let mut writer = get_tag_writer();
        writer
            .write_str("0123456789")
            .expect("Unable to write to PlatformLogWriter");

        writer.copy_bytes_to_start(3, 2);

        assert_eq!(
            unsafe { assume_init_slice(&writer.buffer[..10]) },
            "3423456789".as_bytes()
        );
    }

    #[test]
    fn copy_bytes_to_start_nop() {
        let test_string = "Test_string_with\n\n\n\nnewlines\n";
        let mut writer = get_tag_writer();
        writer
            .write_str(test_string)
            .expect("Unable to write to PlatformLogWriter");

        writer.copy_bytes_to_start(0, 20);
        writer.copy_bytes_to_start(10, 0);

        assert_eq!(
            unsafe { assume_init_slice(&writer.buffer[..test_string.len()]) },
            test_string.as_bytes()
        );
    }

    fn get_tag_writer() -> PlatformLogWriter<'static> {
        PlatformLogWriter::new(
            None,
            Level::Warn,
            CStr::from_bytes_with_nul(b"tag\0").unwrap(),
        )
    }

    unsafe fn assume_init_slice<T>(slice: &[MaybeUninit<T>]) -> &[T] {
        &*(slice as *const [MaybeUninit<T>] as *const [T])
    }
}
