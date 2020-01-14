use nostd_cell::OnceCell;
use std::thread;

static C: OnceCell<u32> = OnceCell::new();

fn main() {
    let t1 = thread::spawn(|| {
        C.set(11).ok();
    });
    C.set(34).ok();
    t1.join().unwrap();
}
