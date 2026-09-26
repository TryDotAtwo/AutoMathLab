# Лёгкие автоматические проверки реестра

Автор: Codex, аудит по поручению владельца. Продолжение участка Issue16/PR20,
пункт E06 аудита. Научная карта и её cutoff не меняются.

Добавлен `.github/workflows/registry-checks.yml`: PR/main, Linux/Windows,
Python3.11, ограничение10минут на job, read-only contents, без сохранения
checkout credentials, actions по точным commit. Запускаются только конкретные
собственные тесты/скрипты реестра. Команды из submitted материалов не исполняются,
научные артефакты не скачиваются, Lean и Telegram не запускаются.

Команды локального воспроизведения:

```sh
python -m unittest discover -s tests -p test_lrx_map.py
python -O -m unittest discover -s tests -p test_lrx_map.py
python scripts/render_lrx_map.py --check
python -O scripts/render_lrx_map.py --check
python scripts/check_materials.py
git diff --check
```

Перед публикацией actions refs проверены через официальный GitHub API:
checkout v7.0.1 — `3d3c42e5aac5ba805825da76410c181273ba90b1`;
setup-python v7.0.0 — `5fda3b95a4ea91299a34e894583c3862153e4b97`.
Это фиксированные версии, а не плавающие major tags.

Локально28 unittest проходят normal/-O, оба generator checks, структурный
валидатор, YAML parse и git diff --check проходят. Независимый read-only review
проверил staged diff, реально вызываемые scripts/tests, trigger/permissions,
оба action refs через GitHub API и git diff --cached --check; блокирующих
замечаний не найдено. Проверяющий не дублировал локальные tests/Lean.

PR исполняет свою версию scripts/tests в обычном CI без привилегий; workflow
не является sandbox для произвольного PR-кода. Изменения этих файлов требуют
review; сторонние научные приложения по данным реестра не запускаются.

Реальный GitHub
Actions run проверяется после push; наличие workflow само по себе не считается
успешным CI. Branch protection/обязательные status checks не настроены этим
изменением. E06 закрывается в main только после интеграции и успешного run.
