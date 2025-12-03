# Dependency Graphs MASAQ

> **⚠️ WARNING: DRAFT WORK**
>
> This repository and its contents are currently in a **DRAFT** state. The code, data, and documentation are subject to change without notice. Use with caution.

**Status: DRAFT**

This repository contains tools to generate dependency graphs for Quranic verses using the MASAQ database.

## Overview

The `generate_dependency_svg.py` script reads Quranic text, morphology, and syntax data from `MASAQ.db` and generates Scalable Vector Graphics (SVG) visualizations of the dependency grammar.

## Usage

1.  **Prerequisites**: Python 3.8+
2.  **Run the script**:

    ```bash
    python3 generate_dependency_svg.py --surah <SURAH_NUMBER> --ayah <AYAH_NUMBER>
    ```

    Example:
    ```bash
    python3 generate_dependency_svg.py --surah 1 --ayah 1
    ```

    This will generate an SVG file in the `output_v2/` directory (created automatically).

3.  **Options**:
    *   `--surah`, `--ayah`: Specify the verse(s) to generate.
    *   `--output`: Specify a custom output path (when using `--spec`).
    *   `--debug`: Enable debug visualization (outlines, overlaps).
    *   `--verbose`: Print detailed logs.

## Sample Output

Here are the generated dependency graphs for Surah Al-Fatiha (Surah 1):

### Ayah 1
![Surah 1 Ayah 1](output_v2/1/1.svg)

### Ayah 2
![Surah 1 Ayah 2](output_v2/1/2.svg)

### Ayah 3
![Surah 1 Ayah 3](output_v2/1/3.svg)

### Ayah 4
![Surah 1 Ayah 4](output_v2/1/4.svg)

### Ayah 5
![Surah 1 Ayah 5](output_v2/1/5.svg)

### Ayah 6
![Surah 1 Ayah 6](output_v2/1/6.svg)

### Ayah 7
![Surah 1 Ayah 7](output_v2/1/7.svg)

## Data Source

This project uses the **MASAQ** dataset:
*   **Title**: MASAQ: Morphologically and Syntactically-Annotated Quran Dataset
*   **Author**: Majdi Sawalha
*   **Source**: [Mendeley Data](https://data.mendeley.com/datasets/9yvrzxktmr/2)
*   **DOI**: 10.17632/9yvrzxktmr.2
*   **Citation**:
    > Sawalha, Majdi (2024), “MASAQ: Morphologically and Syntactically-Annotated Quran Dataset”, Mendeley Data, V2, doi: 10.17632/9yvrzxktmr.2

## Contributing

This project is currently in **DRAFT** status. We welcome contributions!
*   Found a bug? Please open an Issue.
*   Want to improve the graph layout or logic? Please submit a Pull Request.

## License

This project is licensed under the MIT License - see the [LICENSE](LICENSE) file for details.
The `MASAQ.db` file is subject to its own license terms (CC BY 4.0).
