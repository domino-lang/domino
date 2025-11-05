// SPDX-License-Identifier: MIT OR Apache-2.0

//use crate::project::error::Result;
use thiserror::Error;

#[derive(Debug, Error)]
pub enum Error {
    #[error("error parsing utf8: {0}")]
    Utf8Error(#[from] std::string::FromUtf8Error),
    #[error("io error: {0}")]
    IOError(#[from] std::io::Error),
}

type Result<T> = std::result::Result<T, Error>;

use std::io::Read;
use std::io::Write as IOWrite;
use std::mem::swap;
use std::sync::mpsc::Sender;

pub struct Communicator {
    stdout: std::process::ChildStdout,
    chan: Option<std::sync::mpsc::Sender<String>>,
    thrd: Option<std::thread::JoinHandle<Result<()>>>,
    buf: Vec<u8>,
    pos: usize,
}

impl Communicator {
    pub fn new_from_cmd_without_transcript(cmd: std::process::Command) -> Result<Self> {
        Self::new_from_cmd::<Vec<u8>>(cmd, None)
    }

    pub fn new_from_cmd<W: std::io::Write + Send + Sync + 'static>(
        mut cmd: std::process::Command,
        mut transcript: Option<W>,
    ) -> Result<Self> {
        let cmd = cmd.spawn()?;

        let (send, recv) = std::sync::mpsc::channel();

        let mut stdin = cmd.stdin.unwrap();
        let stdout = cmd.stdout.unwrap();

        let thrd = std::thread::spawn(move || {
            writeln!(stdin)?;
            for data in recv {
                if let Some(ref mut transcript) = transcript {
                    write!(transcript, "{data}")?;
                    transcript.flush()?;
                }

                write!(stdin, "{data}")?;
                stdin.flush()?;
            }
            Ok(())
        });

        let buf = vec![0u8; 1 << 20];

        Ok(Communicator {
            stdout,
            chan: Some(send),
            thrd: Some(thrd),
            buf,
            pos: 0,
        })
    }

    pub fn read_until_pred<T, P: Fn(usize, &str) -> (usize, Option<T>)>(
        &mut self,
        p: P,
    ) -> Result<T> {
        loop {
            let read_cnt = self.stdout.read(&mut self.buf[self.pos..])?;
            self.pos += read_cnt;

            let data = String::from_utf8(self.buf[..self.pos].to_vec())?;
            if let (data_read, Some(v)) = p(read_cnt, &data) {
                let rest_bs = data[data_read..].as_bytes().to_owned();

                self.buf.fill(0);
                self.pos = rest_bs.len();
                self.buf[..self.pos].copy_from_slice(&rest_bs);

                return Ok(v);
            }
        }
    }

    pub fn read_until(&mut self, pattern: &str) -> Result<(usize, String)> {
        loop {
            self.pos += self.stdout.read(&mut self.buf[self.pos..])?;
            let data = String::from_utf8(self.buf[..self.pos].to_vec())?;

            if let Some(match_start) = data.find(pattern) {
                let match_end = match_start + pattern.len();

                let ret = data[..match_end].to_string();
                let rest_bs = data[match_end..].as_bytes();

                self.buf.fill(0);
                self.pos = rest_bs.len();
                self.buf[..self.pos].copy_from_slice(rest_bs);

                return Ok((match_start, ret));
            }
        }
    }

    pub fn read_until_end(&mut self) -> Result<String> {
        let mut data = String::from_utf8(self.buf[..self.pos].to_vec())?;
        self.stdout.read_to_string(&mut data)?;
        Ok(data)
    }

    pub fn close(&mut self) {
        let mut none = None;
        swap(&mut self.chan, &mut none)
    }

    pub fn join(&mut self) -> Result<()> {
        if self.thrd.is_none() {
            return Ok(());
        }

        let mut thrd = None;
        swap(&mut thrd, &mut self.thrd);

        thrd.unwrap().join().expect("error joining thread")
    }

    pub fn child_is_finished(&self) -> bool {
        if let Some(thrd) = &self.thrd {
            thrd.is_finished()
        } else {
            // this is only None if we have already joined
            true
        }
    }
}

impl std::fmt::Write for Communicator {
    fn write_str(&mut self, s: &str) -> std::fmt::Result {
        if self.child_is_finished() {
            if let Err(e) = self.join() {
                eprintln!("client finished with a error {e}. last output:");
                std::io::copy(&mut self.stdout, &mut std::io::stderr()).unwrap();
                std::io::stderr().flush().expect("error flushing stderr");

                return Err(std::fmt::Error);
            }
        }

        let chan: &Sender<String> = self.chan.as_ref().expect("writing to closed communicator");

        if chan.send(s.to_string()).is_err() {
            // this means the prover process has quit.
            // it's time to join our thread to get the actual error.

            let thread_result = self.join();
            let rest = self.read_until_end().unwrap();

            eprintln!("result from prover communication thread:\n  {thread_result:?}");
            eprintln!("rest of data from prover:\n  {rest}");
            std::io::stderr().flush().expect("error flushing stderr");

            Err(std::fmt::Error)
        } else {
            Ok(())
        }
    }
}
