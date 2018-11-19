extern crate askama_escape;
#[macro_use]
extern crate criterion;

use askama_escape::escape;
use criterion::Criterion;

criterion_main!(benches);
criterion_group!(benches, functions);

fn functions(c: &mut Criterion) {
    c.bench_function("Format 60 bytes", format_short);
    c.bench_function("Escaping 60 bytes", escaping_short);
    c.bench_function("Format 10 MB", format_long);
    c.bench_function("Escaping 10 MB", escaping_long);
}

static FOO_BAR: &str = "foobar";
static ESCAPES: &str = "<>&\"'/";
static EMPTY: &str = "";

fn escaping_short(b: &mut criterion::Bencher) {
    // 30 bytes at 20% escape
    let string: &str = &[FOO_BAR, FOO_BAR, ESCAPES, FOO_BAR, FOO_BAR].join("");
    let no_escape: &str = &[FOO_BAR; 5].join("");

    b.iter(|| {
        escape(EMPTY).to_string();
        escape(string).to_string();
        escape(no_escape).to_string();
    });
}

fn format_short(b: &mut criterion::Bencher) {
    // 30 bytes at 20% escape
    let string: &str = &[FOO_BAR, FOO_BAR, ESCAPES, FOO_BAR, FOO_BAR].join("");
    let no_escape: &str = &[FOO_BAR; 5].join("");

    b.iter(|| {
        EMPTY.to_string();
        string.to_string();
        no_escape.to_string();
    });
}

fn escaping_long(b: &mut criterion::Bencher) {
    // 5 MB bytes at 20% escape
    let string: &str = &["a>foo"; 1024 * 1024].join("");
    let no_escape: &str = &"a".repeat(5 * 1024 * 1024);

    b.iter(|| {
        escape(string).to_string();
        escape(no_escape).to_string();
    });
}

fn format_long(b: &mut criterion::Bencher) {
    // 5 MB bytes at 20% escape
    let string: &str = &["a>foo"; 1024 * 1024].join("");
    let no_escape: &str = &"a".repeat(5 * 1024 * 1024);

    b.iter(|| {
        string.to_string();
        no_escape.to_string();
    });
}
