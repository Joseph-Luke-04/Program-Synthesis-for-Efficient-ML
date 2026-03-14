FROM ubuntu:22.04

ARG DEBIAN_FRONTEND=noninteractive
ARG CBMC_REPO=https://github.com/diffblue/cbmc.git
ARG CBMC_COMMIT=4737c447653aac8f72921bcfa7779b8b70585eaa
ARG MAMBA_ROOT_PREFIX=/opt/conda

ENV MAMBA_ROOT_PREFIX=${MAMBA_ROOT_PREFIX}
ENV PATH=${MAMBA_ROOT_PREFIX}/bin:/usr/local/bin:${PATH}

SHELL ["/bin/bash", "-lc"]

RUN apt-get update && apt-get install -y --no-install-recommends \
    bash \
    build-essential \
    bison \
    ca-certificates \
    curl \
    file \
    flex \
    git \
    libgmp-dev \
    patch \
    perl \
    pkg-config \
    zlib1g-dev \
    && rm -rf /var/lib/apt/lists/*

RUN curl -Ls https://micro.mamba.pm/api/micromamba/linux-64/latest \
    | tar -xj -C /usr/local/bin --strip-components=1 bin/micromamba

RUN micromamba install -y -n base -c conda-forge \
    python=3.11 \
    pip \
    iverilog \
    pytest \
    jupyter \
    nbconvert \
    ipykernel \
    && micromamba clean --all --yes

WORKDIR /tmp/build

COPY requirements.txt /tmp/build/requirements.txt
RUN pip install --no-cache-dir -r requirements.txt cocotb==2.0.0

RUN git clone "${CBMC_REPO}" /opt/cbmc-hls
WORKDIR /opt/cbmc-hls
RUN git checkout "${CBMC_COMMIT}"

COPY docker/cbmc-solvers.Makefile.patch /tmp/build/cbmc-solvers.Makefile.patch
RUN git apply /tmp/build/cbmc-solvers.Makefile.patch \
    && make -C src minisat2-download \
    && make -C src -j"$(nproc)"

COPY tools/smt2c /tmp/build/smt2c
WORKDIR /tmp/build/smt2c/src
RUN make CPROVER_DIR=/opt/cbmc-hls

RUN mkdir -p /opt/smt2c \
    && cp -R /tmp/build/smt2c/. /opt/smt2c/

WORKDIR /workspace

COPY docker/entrypoint.sh /usr/local/bin/container-entrypoint.sh
RUN chmod +x /usr/local/bin/container-entrypoint.sh

ENTRYPOINT ["/usr/local/bin/container-entrypoint.sh"]
CMD ["bash"]
