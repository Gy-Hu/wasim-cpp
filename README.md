# wasim-cpp

### C++ version of [WASIM](https://link.springer.com/chapter/10.1007/978-3-031-30820-8_2). Also, please find the Python version in [repo](https://github.com/fangwenji/tacas23-wasim)

### WASIM: A Word-level Abstract Symbolic Simulation Framework for Hardware Formal Verification

#### Citation
```
@inproceedings{fang2023wasim,
  title={WASIM: A Word-level Abstract Symbolic Simulation Framework for Hardware Formal Verification},
  author={Fang, Wenji and Zhang, Hongce},
  booktitle={Proceedings of Tools and Algorithms for the Construction and Analysis of Systems (TACAS), Held as Part of the European Joint Conferences on Theory and Practice of Software (ETAPS)},
  pages={11--18},
  year={2023},
  organization={Springer}
}
```


### Prerequisite

    pip3 install toml
    sudo apt install build-essential cmake default-jre libgmp-dev libboost-all-dev libgflags-dev

### SETUP

    ./contrib/setup-glog.sh
    ./contrib/setup-bison.sh
    ./contrib/setup-btor2tools.sh
    ./contrib/setup-smt-switch.sh
    ./configure.sh
    cd build
    make
    
### Usage

For a quick example of how to use the simulator, you may look at `apps/test.cpp`
