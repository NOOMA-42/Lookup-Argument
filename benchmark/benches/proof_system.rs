

use itertools::Itertools;
use std::{
    env::args,
    fmt::{write, Display},
    fs::{create_dir, File, OpenOptions},
    io::{Cursor, Write},
    iter,
    ops::Range,
    path::Path,
    time::{Duration, Instant},
};

use plonkish_backend::{backend::{self,baloo,cq}};



const OUTPUT_DIR: &str = "../target/bench";

fn main() {
    //input some systems,but only one circuit.
    let (systems, k_range) = parse_args();
    create_output(&systems);
    //for each k in k_range,for each system: do benchmark(fn bench)
    k_range.for_each(|k| systems.iter().for_each(|system| system.bench(k)));
}


fn bench_baloo(k: usize) {
    // test_baloo();
    let mut timings =plonkish_backend::backend::baloo::test_baloo_by_k(k);
    // let mut timings =plonkish_backend::backend::baloo::test_baloo_by_k(k);
    for timing in &timings {
        writeln!(&mut System::Baloo.output(), "{}", timing).unwrap(); // 写入每条记录到文件
    }
}

fn bench_CQ(k: usize) {
    // test_baloo();
    let mut timings =plonkish_backend::backend::cq::test_cq_by_k(k);
    for timing in &timings {
        writeln!(&mut System::CQ.output(), "{}", timing).unwrap(); // 写入每条记录到文件
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum System {
    CQ,
    Baloo, //new, To Be Realized
}

impl System {
    fn all() -> Vec<System> {
        vec![
            System::CQ,
            System::Baloo, //new, To Be Realized
        ]
    }

    fn output_path(&self) -> String {
        format!("{OUTPUT_DIR}/{self}")
    }

    fn output(&self) -> File {
        OpenOptions::new()
            .append(true)
            .open(self.output_path())
            .unwrap()
    }

    //for k, circuit, do benchmark for a system.
    fn bench(&self, k: usize) {
        match self {
            System::Baloo => {
                bench_baloo(k) // Call directly without circuit
            }
            System::CQ => {
                bench_CQ(k) // Call directly without circuit
            }
        }
    }
}

impl Display for System {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            System::Baloo => write!(f, "Baloo"), //new, To Be Realized
            System::CQ => write!(f, "CQ"),       //new, To Be Realized
        }
    }
}

fn parse_args() -> (Vec<System>, Range<usize>) {
    let (systems,  k_range) = args().chain(Some("".to_string())).tuple_windows().fold(
        (Vec::new(), 20..26),
        |(mut systems,  mut k_range), (key, value)| {
            match key.as_str() {
                "--system" => match value.as_str() {
                    "all" => systems = System::all(),
                    "cq" => systems.push(System::CQ),
                    "CQ" => systems.push(System::CQ),
                    "Baloo" => systems.push(System::Baloo),
                    "baloo" => systems.push(System::Baloo),                   
                    _ => panic!(
                        "system should be one of {{all,cq,baloo}}"
                    ),
                },
                
                "--k" => {
                    if let Some((start, end)) = value.split_once("..") {
                        k_range = start.parse().expect("k range start to be usize")
                            ..end.parse().expect("k range end to be usize");
                    } else {
                        k_range.start = value.parse().expect("k to be usize");
                        k_range.end = k_range.start + 1;
                    }
                }
                _ => {}
            }
            (systems, k_range)
        },
    );

    let mut systems = systems.into_iter().sorted().dedup().collect_vec();
    if systems.is_empty() {
        systems = System::all();
    };
    (systems, k_range)
}

fn create_output(systems: &[System]) {
    if !Path::new(OUTPUT_DIR).exists() {
        create_dir(OUTPUT_DIR).unwrap();
    }
    for system in systems {
        File::create(system.output_path()).unwrap();
    }
}
