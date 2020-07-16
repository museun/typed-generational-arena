#[macro_use]
extern crate criterion;
extern crate typed_generational_arena;

use criterion::{Criterion, ParameterizedBenchmark, Throughput};
use typed_generational_arena::{
    PtrSlab, PtrSlabIndex, SmallPtrSlab, SmallPtrSlabIndex, SmallSlab, SmallSlabIndex,
    StandardSlab as Slab, StandardSlabIndex as SlabIndex,
};
use typed_generational_arena::{
    SmallArena, SmallIndex, StandardArena as Arena, StandardIndex as Index,
};

#[derive(Default)]
struct Small(usize);

#[derive(Default)]
struct Big([usize; 32]);

fn insert<T: Default>(n: usize) {
    let mut arena = Arena::<T>::new();
    for _ in 0..n {
        let idx = arena.insert(Default::default());
        criterion::black_box(idx);
    }
}

fn lookup<T>(arena: &Arena<T>, idx: Index<T>, n: usize) {
    for _ in 0..n {
        criterion::black_box(&arena[idx]);
    }
}

fn collect<T>(arena: &Arena<T>, n: usize) {
    for _ in 0..n {
        criterion::black_box(arena.iter().collect::<Vec<_>>());
    }
}

fn u32_insert<T: Default>(n: usize) {
    let mut arena = SmallArena::<T>::new();
    for _ in 0..n {
        let idx = arena.insert(Default::default());
        criterion::black_box(idx);
    }
}

fn u32_lookup<T>(arena: &SmallArena<T>, idx: SmallIndex<T>, n: usize) {
    for _ in 0..n {
        criterion::black_box(&arena[idx]);
    }
}

fn u32_collect<T>(arena: &SmallArena<T>, n: usize) {
    for _ in 0..n {
        criterion::black_box(arena.iter().collect::<Vec<_>>());
    }
}

fn slab_insert<T: Default>(n: usize) {
    let mut slab = Slab::<T>::new();
    for _ in 0..n {
        let idx = slab.insert(Default::default());
        criterion::black_box(idx);
    }
}

fn slab_lookup<T>(slab: &Slab<T>, idx: SlabIndex<T>, n: usize) {
    for _ in 0..n {
        criterion::black_box(&slab[idx]);
    }
}

fn slab_collect<T>(slab: &Slab<T>, n: usize) {
    for _ in 0..n {
        criterion::black_box(slab.iter().collect::<Vec<_>>());
    }
}

fn u32_slab_insert<T: Default>(n: usize) {
    let mut slab = SmallSlab::<T>::new();
    for _ in 0..n {
        let idx = slab.insert(Default::default());
        criterion::black_box(idx);
    }
}

fn u32_slab_lookup<T>(slab: &SmallSlab<T>, idx: SmallSlabIndex<T>, n: usize) {
    for _ in 0..n {
        criterion::black_box(&slab[idx]);
    }
}

fn u32_slab_collect<T>(slab: &SmallSlab<T>, n: usize) {
    for _ in 0..n {
        criterion::black_box(slab.iter().collect::<Vec<_>>());
    }
}

fn ptr_slab_insert<T: Default>(n: usize) {
    let mut slab = PtrSlab::<T>::new();
    for _ in 0..n {
        let idx = slab.insert(Default::default());
        criterion::black_box(idx);
    }
}

fn ptr_slab_lookup<T>(slab: &PtrSlab<T>, idx: PtrSlabIndex<T>, n: usize) {
    for _ in 0..n {
        criterion::black_box(&slab[idx]);
    }
}

fn ptr_slab_collect<T>(slab: &PtrSlab<T>, n: usize) {
    for _ in 0..n {
        criterion::black_box(slab.iter().collect::<Vec<_>>());
    }
}

fn u32_ptr_slab_insert<T: Default>(n: usize) {
    let mut slab = SmallPtrSlab::<T>::new();
    for _ in 0..n {
        let idx = slab.insert(Default::default());
        criterion::black_box(idx);
    }
}

fn u32_ptr_slab_lookup<T>(slab: &SmallPtrSlab<T>, idx: SmallPtrSlabIndex<T>, n: usize) {
    for _ in 0..n {
        criterion::black_box(&slab[idx]);
    }
}

fn u32_ptr_slab_collect<T>(slab: &SmallPtrSlab<T>, n: usize) {
    for _ in 0..n {
        criterion::black_box(slab.iter().collect::<Vec<_>>());
    }
}

fn criterion_benchmark(c: &mut Criterion) {
    c.bench(
        "insert",
        ParameterizedBenchmark::new(
            "insert-small",
            |b, n| b.iter(|| insert::<Small>(*n)),
            (1..3).map(|n| n * 100).collect::<Vec<usize>>(),
        )
        .throughput(|n| Throughput::Elements(*n as u32)),
    );

    c.bench(
        "insert",
        ParameterizedBenchmark::new(
            "insert-big",
            |b, n| b.iter(|| insert::<Big>(*n)),
            (1..3).map(|n| n * 100).collect::<Vec<usize>>(),
        )
        .throughput(|n| Throughput::Elements(*n as u32)),
    );

    c.bench(
        "lookup",
        ParameterizedBenchmark::new(
            "lookup-small",
            |b, n| {
                let mut small_arena = Arena::<Small>::new();
                for _ in 0..1024 {
                    small_arena.insert(Default::default());
                }
                let small_idx = small_arena.iter().map(|pair| pair.0).next().unwrap();
                b.iter(|| lookup(&small_arena, small_idx, *n))
            },
            (1..3).map(|n| n * 100).collect::<Vec<usize>>(),
        )
        .throughput(|n| Throughput::Elements(*n as u32)),
    );

    c.bench(
        "lookup",
        ParameterizedBenchmark::new(
            "lookup-big",
            |b, n| {
                let mut big_arena = Arena::<Big>::new();
                for _ in 0..1024 {
                    big_arena.insert(Default::default());
                }
                let big_idx = big_arena.iter().map(|pair| pair.0).next().unwrap();
                b.iter(|| lookup(&big_arena, big_idx, *n))
            },
            (1..3).map(|n| n * 100).collect::<Vec<usize>>(),
        )
        .throughput(|n| Throughput::Elements(*n as u32)),
    );

    c.bench(
        "collect",
        ParameterizedBenchmark::new(
            "collect-small",
            |b, n| {
                let mut small_arena = Arena::<Small>::new();
                for _ in 0..1024 {
                    small_arena.insert(Default::default());
                }
                b.iter(|| collect(&small_arena, *n))
            },
            (1..3).map(|n| n * 100).collect::<Vec<usize>>(),
        )
        .throughput(|n| Throughput::Elements(*n as u32)),
    );

    c.bench(
        "collect",
        ParameterizedBenchmark::new(
            "collect-big",
            |b, n| {
                let mut big_arena = Arena::<Big>::new();
                for _ in 0..1024 {
                    big_arena.insert(Default::default());
                }
                b.iter(|| collect(&big_arena, *n))
            },
            (1..3).map(|n| n * 100).collect::<Vec<usize>>(),
        )
        .throughput(|n| Throughput::Elements(*n as u32)),
    );

    c.bench(
        "insert",
        ParameterizedBenchmark::new(
            "slab-insert-small",
            |b, n| b.iter(|| slab_insert::<Small>(*n)),
            (1..3).map(|n| n * 100).collect::<Vec<usize>>(),
        )
        .throughput(|n| Throughput::Elements(*n as u32)),
    );

    c.bench(
        "insert",
        ParameterizedBenchmark::new(
            "slab-insert-big",
            |b, n| b.iter(|| slab_insert::<Big>(*n)),
            (1..3).map(|n| n * 100).collect::<Vec<usize>>(),
        )
        .throughput(|n| Throughput::Elements(*n as u32)),
    );

    c.bench(
        "lookup",
        ParameterizedBenchmark::new(
            "slab-lookup-small",
            |b, n| {
                let mut small_slab = Slab::<Small>::new();
                for _ in 0..1024 {
                    small_slab.insert(Default::default());
                }
                let small_idx = small_slab.iter().map(|pair| pair.0).next().unwrap();
                b.iter(|| slab_lookup(&small_slab, small_idx, *n))
            },
            (1..3).map(|n| n * 100).collect::<Vec<usize>>(),
        )
        .throughput(|n| Throughput::Elements(*n as u32)),
    );

    c.bench(
        "lookup",
        ParameterizedBenchmark::new(
            "slab-lookup-big",
            |b, n| {
                let mut big_slab = Slab::<Big>::new();
                for _ in 0..1024 {
                    big_slab.insert(Default::default());
                }
                let big_idx = big_slab.iter().map(|pair| pair.0).next().unwrap();
                b.iter(|| slab_lookup(&big_slab, big_idx, *n))
            },
            (1..3).map(|n| n * 100).collect::<Vec<usize>>(),
        )
        .throughput(|n| Throughput::Elements(*n as u32)),
    );

    c.bench(
        "collect",
        ParameterizedBenchmark::new(
            "slab-collect-small",
            |b, n| {
                let mut small_slab = Slab::<Small>::new();
                for _ in 0..1024 {
                    small_slab.insert(Default::default());
                }
                b.iter(|| slab_collect(&small_slab, *n))
            },
            (1..3).map(|n| n * 100).collect::<Vec<usize>>(),
        )
        .throughput(|n| Throughput::Elements(*n as u32)),
    );

    c.bench(
        "collect",
        ParameterizedBenchmark::new(
            "slab-collect-big",
            |b, n| {
                let mut big_slab = Slab::<Big>::new();
                for _ in 0..1024 {
                    big_slab.insert(Default::default());
                }
                b.iter(|| slab_collect(&big_slab, *n))
            },
            (1..3).map(|n| n * 100).collect::<Vec<usize>>(),
        )
        .throughput(|n| Throughput::Elements(*n as u32)),
    );

    c.bench(
        "insert",
        ParameterizedBenchmark::new(
            "u32-insert-small",
            |b, n| b.iter(|| u32_insert::<Small>(*n)),
            (1..3).map(|n| n * 100).collect::<Vec<usize>>(),
        )
        .throughput(|n| Throughput::Elements(*n as u32)),
    );

    c.bench(
        "insert",
        ParameterizedBenchmark::new(
            "u32-insert-big",
            |b, n| b.iter(|| u32_insert::<Big>(*n)),
            (1..3).map(|n| n * 100).collect::<Vec<usize>>(),
        )
        .throughput(|n| Throughput::Elements(*n as u32)),
    );

    c.bench(
        "lookup",
        ParameterizedBenchmark::new(
            "u32-lookup-small",
            |b, n| {
                let mut small_arena = SmallArena::<Small>::new();
                for _ in 0..1024 {
                    small_arena.insert(Default::default());
                }
                let small_idx = small_arena.iter().map(|pair| pair.0).next().unwrap();
                b.iter(|| u32_lookup(&small_arena, small_idx, *n))
            },
            (1..3).map(|n| n * 100).collect::<Vec<usize>>(),
        )
        .throughput(|n| Throughput::Elements(*n as u32)),
    );

    c.bench(
        "lookup",
        ParameterizedBenchmark::new(
            "u32-lookup-big",
            |b, n| {
                let mut big_arena = SmallArena::<Big>::new();
                for _ in 0..1024 {
                    big_arena.insert(Default::default());
                }
                let big_idx = big_arena.iter().map(|pair| pair.0).next().unwrap();
                b.iter(|| u32_lookup(&big_arena, big_idx, *n))
            },
            (1..3).map(|n| n * 100).collect::<Vec<usize>>(),
        )
        .throughput(|n| Throughput::Elements(*n as u32)),
    );

    c.bench(
        "collect",
        ParameterizedBenchmark::new(
            "u32-collect-small",
            |b, n| {
                let mut small_arena = SmallArena::<Small>::new();
                for _ in 0..1024 {
                    small_arena.insert(Default::default());
                }
                b.iter(|| u32_collect(&small_arena, *n))
            },
            (1..3).map(|n| n * 100).collect::<Vec<usize>>(),
        )
        .throughput(|n| Throughput::Elements(*n as u32)),
    );

    c.bench(
        "collect",
        ParameterizedBenchmark::new(
            "u32-collect-big",
            |b, n| {
                let mut big_arena = SmallArena::<Big>::new();
                for _ in 0..1024 {
                    big_arena.insert(Default::default());
                }
                b.iter(|| u32_collect(&big_arena, *n))
            },
            (1..3).map(|n| n * 100).collect::<Vec<usize>>(),
        )
        .throughput(|n| Throughput::Elements(*n as u32)),
    );

    c.bench(
        "insert",
        ParameterizedBenchmark::new(
            "u32-slab-insert-small",
            |b, n| b.iter(|| u32_slab_insert::<Small>(*n)),
            (1..3).map(|n| n * 100).collect::<Vec<usize>>(),
        )
        .throughput(|n| Throughput::Elements(*n as u32)),
    );

    c.bench(
        "insert",
        ParameterizedBenchmark::new(
            "u32-slab-insert-big",
            |b, n| b.iter(|| u32_slab_insert::<Big>(*n)),
            (1..3).map(|n| n * 100).collect::<Vec<usize>>(),
        )
        .throughput(|n| Throughput::Elements(*n as u32)),
    );

    c.bench(
        "lookup",
        ParameterizedBenchmark::new(
            "u32-slab-lookup-small",
            |b, n| {
                let mut small_slab = SmallSlab::<Small>::new();
                for _ in 0..1024 {
                    small_slab.insert(Default::default());
                }
                let small_idx = small_slab.iter().map(|pair| pair.0).next().unwrap();
                b.iter(|| u32_slab_lookup(&small_slab, small_idx, *n))
            },
            (1..3).map(|n| n * 100).collect::<Vec<usize>>(),
        )
        .throughput(|n| Throughput::Elements(*n as u32)),
    );

    c.bench(
        "lookup",
        ParameterizedBenchmark::new(
            "u32-slab-lookup-big",
            |b, n| {
                let mut big_slab = SmallSlab::<Big>::new();
                for _ in 0..1024 {
                    big_slab.insert(Default::default());
                }
                let big_idx = big_slab.iter().map(|pair| pair.0).next().unwrap();
                b.iter(|| u32_slab_lookup(&big_slab, big_idx, *n))
            },
            (1..3).map(|n| n * 100).collect::<Vec<usize>>(),
        )
        .throughput(|n| Throughput::Elements(*n as u32)),
    );

    c.bench(
        "collect",
        ParameterizedBenchmark::new(
            "u32-slab-collect-small",
            |b, n| {
                let mut small_slab = SmallSlab::<Small>::new();
                for _ in 0..1024 {
                    small_slab.insert(Default::default());
                }
                b.iter(|| u32_slab_collect(&small_slab, *n))
            },
            (1..3).map(|n| n * 100).collect::<Vec<usize>>(),
        )
        .throughput(|n| Throughput::Elements(*n as u32)),
    );

    c.bench(
        "collect",
        ParameterizedBenchmark::new(
            "u32-slab-collect-big",
            |b, n| {
                let mut big_slab = SmallSlab::<Big>::new();
                for _ in 0..1024 {
                    big_slab.insert(Default::default());
                }
                b.iter(|| u32_slab_collect(&big_slab, *n))
            },
            (1..3).map(|n| n * 100).collect::<Vec<usize>>(),
        )
        .throughput(|n| Throughput::Elements(*n as u32)),
    );

    c.bench(
        "insert",
        ParameterizedBenchmark::new(
            "ptr-slab-insert-small",
            |b, n| b.iter(|| ptr_slab_insert::<Small>(*n)),
            (1..3).map(|n| n * 100).collect::<Vec<usize>>(),
        )
        .throughput(|n| Throughput::Elements(*n as u32)),
    );

    c.bench(
        "insert",
        ParameterizedBenchmark::new(
            "ptr-slab-insert-big",
            |b, n| b.iter(|| ptr_slab_insert::<Big>(*n)),
            (1..3).map(|n| n * 100).collect::<Vec<usize>>(),
        )
        .throughput(|n| Throughput::Elements(*n as u32)),
    );

    c.bench(
        "lookup",
        ParameterizedBenchmark::new(
            "ptr-slab-lookup-small",
            |b, n| {
                let mut small_slab = PtrSlab::<Small>::new();
                for _ in 0..1024 {
                    small_slab.insert(Default::default());
                }
                let small_idx = small_slab.iter().map(|pair| pair.0).next().unwrap();
                b.iter(|| ptr_slab_lookup(&small_slab, small_idx, *n))
            },
            (1..3).map(|n| n * 100).collect::<Vec<usize>>(),
        )
        .throughput(|n| Throughput::Elements(*n as u32)),
    );

    c.bench(
        "lookup",
        ParameterizedBenchmark::new(
            "ptr-slab-lookup-big",
            |b, n| {
                let mut big_slab = PtrSlab::<Big>::new();
                for _ in 0..1024 {
                    big_slab.insert(Default::default());
                }
                let big_idx = big_slab.iter().map(|pair| pair.0).next().unwrap();
                b.iter(|| ptr_slab_lookup(&big_slab, big_idx, *n))
            },
            (1..3).map(|n| n * 100).collect::<Vec<usize>>(),
        )
        .throughput(|n| Throughput::Elements(*n as u32)),
    );

    c.bench(
        "collect",
        ParameterizedBenchmark::new(
            "ptr-slab-collect-small",
            |b, n| {
                let mut small_slab = PtrSlab::<Small>::new();
                for _ in 0..1024 {
                    small_slab.insert(Default::default());
                }
                b.iter(|| ptr_slab_collect(&small_slab, *n))
            },
            (1..3).map(|n| n * 100).collect::<Vec<usize>>(),
        )
        .throughput(|n| Throughput::Elements(*n as u32)),
    );

    c.bench(
        "collect",
        ParameterizedBenchmark::new(
            "ptr-slab-collect-big",
            |b, n| {
                let mut big_slab = PtrSlab::<Big>::new();
                for _ in 0..1024 {
                    big_slab.insert(Default::default());
                }
                b.iter(|| ptr_slab_collect(&big_slab, *n))
            },
            (1..3).map(|n| n * 100).collect::<Vec<usize>>(),
        )
        .throughput(|n| Throughput::Elements(*n as u32)),
    );

    c.bench(
        "insert",
        ParameterizedBenchmark::new(
            "u32-ptr-slab-insert-small",
            |b, n| b.iter(|| u32_ptr_slab_insert::<Small>(*n)),
            (1..3).map(|n| n * 100).collect::<Vec<usize>>(),
        )
        .throughput(|n| Throughput::Elements(*n as u32)),
    );

    c.bench(
        "insert",
        ParameterizedBenchmark::new(
            "u32-ptr-slab-insert-big",
            |b, n| b.iter(|| u32_ptr_slab_insert::<Big>(*n)),
            (1..3).map(|n| n * 100).collect::<Vec<usize>>(),
        )
        .throughput(|n| Throughput::Elements(*n as u32)),
    );

    c.bench(
        "lookup",
        ParameterizedBenchmark::new(
            "u32-ptr-slab-lookup-small",
            |b, n| {
                let mut small_slab = SmallPtrSlab::<Small>::new();
                for _ in 0..1024 {
                    small_slab.insert(Default::default());
                }
                let small_idx = small_slab.iter().map(|pair| pair.0).next().unwrap();
                b.iter(|| u32_ptr_slab_lookup(&small_slab, small_idx, *n))
            },
            (1..3).map(|n| n * 100).collect::<Vec<usize>>(),
        )
        .throughput(|n| Throughput::Elements(*n as u32)),
    );

    c.bench(
        "lookup",
        ParameterizedBenchmark::new(
            "u32-ptr-slab-lookup-big",
            |b, n| {
                let mut big_slab = SmallPtrSlab::<Big>::new();
                for _ in 0..1024 {
                    big_slab.insert(Default::default());
                }
                let big_idx = big_slab.iter().map(|pair| pair.0).next().unwrap();
                b.iter(|| u32_ptr_slab_lookup(&big_slab, big_idx, *n))
            },
            (1..3).map(|n| n * 100).collect::<Vec<usize>>(),
        )
        .throughput(|n| Throughput::Elements(*n as u32)),
    );

    c.bench(
        "collect",
        ParameterizedBenchmark::new(
            "u32-ptr-slab-collect-small",
            |b, n| {
                let mut small_slab = SmallPtrSlab::<Small>::new();
                for _ in 0..1024 {
                    small_slab.insert(Default::default());
                }
                b.iter(|| u32_ptr_slab_collect(&small_slab, *n))
            },
            (1..3).map(|n| n * 100).collect::<Vec<usize>>(),
        )
        .throughput(|n| Throughput::Elements(*n as u32)),
    );

    c.bench(
        "collect",
        ParameterizedBenchmark::new(
            "u32-ptr-slab-collect-big",
            |b, n| {
                let mut big_slab = SmallPtrSlab::<Big>::new();
                for _ in 0..1024 {
                    big_slab.insert(Default::default());
                }
                b.iter(|| u32_ptr_slab_collect(&big_slab, *n))
            },
            (1..3).map(|n| n * 100).collect::<Vec<usize>>(),
        )
        .throughput(|n| Throughput::Elements(*n as u32)),
    );
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
