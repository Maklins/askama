#![cfg_attr(feature = "cargo-clippy", allow(unused_parens))]

extern crate askama_escape;
extern crate num_traits;
extern crate serde;
#[macro_use]
extern crate serde_derive;
#[cfg(feature = "serde-json")]
extern crate serde_json;
extern crate toml;

use std::env;
use std::fs;
use std::path::{Path, PathBuf};

mod error;

pub use askama_escape::MarkupDisplay;
pub use error::{Error, Result};

use std::collections::BTreeMap;

pub mod filters;

#[derive(Debug)]
pub struct Config<'a> {
    pub dirs: Vec<PathBuf>,
    pub syntaxes: BTreeMap<String, Syntax<'a>>,
    pub default_syntax: &'a str,
}

impl<'a> Config<'a> {
    pub fn new(s: &str) -> Config {
        let root = PathBuf::from(env::var("CARGO_MANIFEST_DIR").unwrap());
        let default_dirs = vec![root.join("templates")];

        let mut syntaxes = BTreeMap::new();
        syntaxes.insert(DEFAULT_SYNTAX_NAME.to_string(), Syntax::default());

        let raw: RawConfig =
            toml::from_str(&s).expect(&format!("invalid TOML in {}", CONFIG_FILE_NAME));

        let (dirs, default_syntax) = match raw.general {
            Some(General {
                dirs,
                default_syntax,
            }) => (
                dirs.map_or(default_dirs, |v| {
                    v.into_iter().map(|dir| root.join(dir)).collect()
                }),
                default_syntax.unwrap_or(DEFAULT_SYNTAX_NAME),
            ),
            None => (default_dirs, DEFAULT_SYNTAX_NAME),
        };

        if let Some(raw_syntaxes) = raw.syntax {
            for raw_s in raw_syntaxes {
                let name = raw_s.name;

                if let Some(_) = syntaxes.insert(name.to_string(), Syntax::from(raw_s)) {
                    panic!("syntax \"{}\" is already defined", name)
                }
            }
        }

        if !syntaxes.contains_key(default_syntax) {
            panic!("default syntax \"{}\" not found", default_syntax)
        }

        Config {
            dirs,
            syntaxes,
            default_syntax,
        }
    }

    pub fn find_template(&self, path: &str, start_at: Option<&Path>) -> PathBuf {
        if let Some(root) = start_at {
            let relative = root.with_file_name(path);
            if relative.exists() {
                return relative.to_owned();
            }
        }

        for dir in &self.dirs {
            let rooted = dir.join(path);
            if rooted.exists() {
                return rooted;
            }
        }

        panic!(
            "template {:?} not found in directories {:?}",
            path, self.dirs
        )
    }
}

#[derive(Debug)]
pub struct Syntax<'a> {
    pub block_start: &'a str,
    pub block_end: &'a str,
    pub expr_start: &'a str,
    pub expr_end: &'a str,
    pub comment_start: &'a str,
    pub comment_end: &'a str,
}

impl<'a> Default for Syntax<'a> {
    fn default() -> Self {
        Self {
            block_start: "{%",
            block_end: "%}",
            expr_start: "{{",
            expr_end: "}}",
            comment_start: "{#",
            comment_end: "#}",
        }
    }
}

impl<'a> From<RawSyntax<'a>> for Syntax<'a> {
    fn from(raw: RawSyntax<'a>) -> Self {
        let default = Self::default();
        let syntax = Self {
            block_start: raw.block_start.unwrap_or(default.block_start),
            block_end: raw.block_end.unwrap_or(default.block_end),
            expr_start: raw.expr_start.unwrap_or(default.expr_start),
            expr_end: raw.expr_end.unwrap_or(default.expr_end),
            comment_start: raw.comment_start.unwrap_or(default.comment_start),
            comment_end: raw.comment_end.unwrap_or(default.comment_end),
        };

        if syntax.block_start.len() != 2
            || syntax.block_end.len() != 2
            || syntax.expr_start.len() != 2
            || syntax.expr_end.len() != 2
            || syntax.comment_start.len() != 2
            || syntax.comment_end.len() != 2
        {
            panic!("length of delimiters must be two")
        }

        let bs = syntax.block_start.as_bytes()[0];
        let be = syntax.block_start.as_bytes()[1];
        let cs = syntax.comment_start.as_bytes()[0];
        let ce = syntax.comment_start.as_bytes()[1];
        let es = syntax.block_start.as_bytes()[0];
        let ee = syntax.block_start.as_bytes()[1];
        if !(bs == cs && bs == es) && !(be == ce && be == ee) {
            panic!("bad delimiters block_start: {}, comment_start: {}, expr_start: {}, needs one of the two characters in common", syntax.block_start, syntax.comment_start, syntax.expr_start);
        }

        syntax
    }
}

#[derive(Deserialize)]
struct RawConfig<'d> {
    #[serde(borrow)]
    general: Option<General<'d>>,
    syntax: Option<Vec<RawSyntax<'d>>>,
}

#[derive(Deserialize)]
struct General<'a> {
    #[serde(borrow)]
    dirs: Option<Vec<&'a str>>,
    default_syntax: Option<&'a str>,
}

#[derive(Deserialize)]
struct RawSyntax<'a> {
    name: &'a str,
    block_start: Option<&'a str>,
    block_end: Option<&'a str>,
    expr_start: Option<&'a str>,
    expr_end: Option<&'a str>,
    comment_start: Option<&'a str>,
    comment_end: Option<&'a str>,
}

pub fn read_config_file() -> String {
    let root = PathBuf::from(env::var("CARGO_MANIFEST_DIR").unwrap());
    let filename = root.join(CONFIG_FILE_NAME);
    if filename.exists() {
        fs::read_to_string(&filename)
            .expect(&format!("unable to read {}", filename.to_str().unwrap()))
    } else {
        "".to_string()
    }
}

static CONFIG_FILE_NAME: &str = "askama.toml";
static DEFAULT_SYNTAX_NAME: &str = "default";

#[cfg(test)]
mod tests {
    use super::*;
    use std::env;
    use std::path::{Path, PathBuf};

    #[test]
    fn test_default_config() {
        let mut root = PathBuf::from(env::var("CARGO_MANIFEST_DIR").unwrap());
        root.push("templates");
        let config = Config::new("");
        assert_eq!(config.dirs, vec![root]);
    }

    #[test]
    fn test_config_dirs() {
        let mut root = PathBuf::from(env::var("CARGO_MANIFEST_DIR").unwrap());
        root.push("tpl");
        let config = Config::new("[general]\ndirs = [\"tpl\"]");
        assert_eq!(config.dirs, vec![root]);
    }

    fn assert_eq_rooted(actual: &Path, expected: &str) {
        let mut root = PathBuf::from(env::var("CARGO_MANIFEST_DIR").unwrap());
        root.push("templates");
        let mut inner = PathBuf::new();
        inner.push(expected);
        assert_eq!(actual.strip_prefix(root).unwrap(), inner);
    }

    #[test]
    fn find_absolute() {
        let config = Config::new("");
        let root = config.find_template("a.html", None);
        let path = config.find_template("sub/b.html", Some(&root));
        assert_eq_rooted(&path, "sub/b.html");
    }

    #[test]
    #[should_panic]
    fn find_relative_nonexistent() {
        let config = Config::new("");
        let root = config.find_template("a.html", None);
        config.find_template("b.html", Some(&root));
    }

    #[test]
    fn find_relative() {
        let config = Config::new("");
        let root = config.find_template("sub/b.html", None);
        let path = config.find_template("c.html", Some(&root));
        assert_eq_rooted(&path, "sub/c.html");
    }

    #[test]
    fn find_relative_sub() {
        let config = Config::new("");
        let root = config.find_template("sub/b.html", None);
        let path = config.find_template("sub1/d.html", Some(&root));
        assert_eq_rooted(&path, "sub/sub1/d.html");
    }

    #[test]
    fn add_syntax() {
        let raw_config = r#"
        [general]
        default_syntax = "foo"

        [[syntax]]
        name = "foo"
        block_start = "{<"

        [[syntax]]
        name = "bar"
        expr_start = "{!"
        "#;

        let default_syntax = Syntax::default();
        let config = Config::new(raw_config);
        assert_eq!(config.default_syntax, "foo");

        let foo = config.syntaxes.get("foo").unwrap();
        assert_eq!(foo.block_start, "{<");
        assert_eq!(foo.block_end, default_syntax.block_end);
        assert_eq!(foo.expr_start, default_syntax.expr_start);
        assert_eq!(foo.expr_end, default_syntax.expr_end);
        assert_eq!(foo.comment_start, default_syntax.comment_start);
        assert_eq!(foo.comment_end, default_syntax.comment_end);

        let bar = config.syntaxes.get("bar").unwrap();
        assert_eq!(bar.block_start, default_syntax.block_start);
        assert_eq!(bar.block_end, default_syntax.block_end);
        assert_eq!(bar.expr_start, "{!");
        assert_eq!(bar.expr_end, default_syntax.expr_end);
        assert_eq!(bar.comment_start, default_syntax.comment_start);
        assert_eq!(bar.comment_end, default_syntax.comment_end);
    }

    #[test]
    fn add_syntax_two() {
        let raw_config = r#"
        syntax = [{ name = "foo", block_start = "{<" },
                  { name = "bar", expr_start = "{!" } ]

        [general]
        default_syntax = "foo"
        "#;

        let default_syntax = Syntax::default();
        let config = Config::new(raw_config);
        assert_eq!(config.default_syntax, "foo");

        let foo = config.syntaxes.get("foo").unwrap();
        assert_eq!(foo.block_start, "{<");
        assert_eq!(foo.block_end, default_syntax.block_end);
        assert_eq!(foo.expr_start, default_syntax.expr_start);
        assert_eq!(foo.expr_end, default_syntax.expr_end);
        assert_eq!(foo.comment_start, default_syntax.comment_start);
        assert_eq!(foo.comment_end, default_syntax.comment_end);

        let bar = config.syntaxes.get("bar").unwrap();
        assert_eq!(bar.block_start, default_syntax.block_start);
        assert_eq!(bar.block_end, default_syntax.block_end);
        assert_eq!(bar.expr_start, "{!");
        assert_eq!(bar.expr_end, default_syntax.expr_end);
        assert_eq!(bar.comment_start, default_syntax.comment_start);
        assert_eq!(bar.comment_end, default_syntax.comment_end);
    }

    #[should_panic]
    #[test]
    fn use_default_at_syntax_name() {
        let raw_config = r#"
        syntax = [{ name = "default" }]
        "#;

        let _config = Config::new(raw_config);
    }

    #[should_panic]
    #[test]
    fn duplicated_syntax_name_on_list() {
        let raw_config = r#"
        syntax = [{ name = "foo", block_start = "~<" },
                  { name = "foo", block_start = "%%" } ]
        "#;

        let _config = Config::new(raw_config);
    }

    #[should_panic]
    #[test]
    fn is_not_exist_default_syntax() {
        let raw_config = r#"
        [general]
        default_syntax = "foo"
        "#;

        let _config = Config::new(raw_config);
    }
}
