FROM ubuntu:22.04
ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update && apt-get install -y --no-install-recommends ca-certificates curl git sudo build-essential cmake ninja-build pkg-config python3 python3-pip libboost-all-dev libgmp-dev zlib1g-dev libtbb-dev nauty z3 minisat && rm -rf /var/lib/apt/lists/*
RUN python3 -m pip install --no-cache-dir --upgrade pip setuptools wheel
RUN python3 -m pip install --no-cache-dir 'numpy>=1.26,<3' 'networkx>=3,<4' 'python-sat>=1.8.dev13'
WORKDIR /tmp/sms-build
COPY jobs/erdos-64-sms-direct/setup.sh /tmp/sms-setup.sh
RUN bash /tmp/sms-setup.sh && rm -rf /tmp/sms-build /tmp/sms-setup.sh /var/lib/apt/lists/*
ENV MATH_COMPUTE_SMS_REV=464f12f
ENV PATH="/root/.local/bin:$PATH" PYTHONPATH="/root/.local/lib/python3.10/site-packages" LD_LIBRARY_PATH="/root/.local/lib"
RUN python3 -c 'from pysms.graph_builder import GraphEncodingBuilder; import pysat,networkx,numpy' && command -v smsg && command -v z3 && command -v minisat && command -v nauty-geng

# Number theory, graph algorithms, optimization, and additional SAT/SMT solvers.
RUN apt-get update && apt-get install -y --no-install-recommends cryptominisat bliss pari-gp && rm -rf /var/lib/apt/lists/*
RUN python3 -m pip install --no-cache-dir \
    'ortools>=9.12,<10' 'scipy>=1.12,<2' 'sympy>=1.13,<2' \
    'igraph>=0.11,<0.12' 'gmpy2>=2.1,<3' 'python-flint>=0.8,<1' \
    'cvc5>=1.3,<2' 'z3-solver>=4.13,<5'
# Compile checked-out revisions so solver builds can be reproduced.
RUN git init -q /tmp/kissat && git -C /tmp/kissat remote add origin https://github.com/arminbiere/kissat.git && \
    git -C /tmp/kissat fetch -q --depth 1 origin 8af8e56f174b778aef3aa45af9f739b2a5f492c2 && \
    git -C /tmp/kissat checkout -q FETCH_HEAD && cd /tmp/kissat && ./configure && make -j2 && \
    install -m 0755 build/kissat /usr/local/bin/kissat && rm -rf /tmp/kissat
RUN git init -q /tmp/drat-trim && git -C /tmp/drat-trim remote add origin https://github.com/marijnheule/drat-trim.git && \
    git -C /tmp/drat-trim fetch -q --depth 1 origin 2e3b2dc0ecf938addbd779d42877b6ed69d9a985 && \
    git -C /tmp/drat-trim checkout -q FETCH_HEAD && make -C /tmp/drat-trim -j2 drat-trim lrat-check && \
    install -m 0755 /tmp/drat-trim/drat-trim /tmp/drat-trim/lrat-check /usr/local/bin/ && rm -rf /tmp/drat-trim
COPY containers/test-math-tools.py /opt/math-toolbox/test-math-tools.py
RUN python3 /opt/math-toolbox/test-math-tools.py && python3 -m pip freeze > /opt/math-toolbox/python-requirements.txt
WORKDIR /work
