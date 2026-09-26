# Проверка общего пакета

Из корня распакованного архива:

```sh
python3 research/lower-bound-native-20260925/verify_complete.py
python3 research/lower-bound-native-20260925/rebuild_complete.py \
  --lean /path/to/lean-4.34.0/bin/lean \
  --packages-directory /path/to/pinned/formal/.lake/packages \
  --output-directory /path/to/new-empty-output
```

Нужен существующий Mathlib/package cache по вложенным toolchain и manifest.
Скрипт не устанавливает пакеты и не использует сеть. Все локальные LRX-модули
собираются заново, старые локальные `.olean` не используются. В архиве бинарных
объектов нет. Проверка хешей не заменяет повторную kernel-сборку.

Главный файл `formal/LRX/LowerBoundNativeComplete.lean`; главный экспорт
`LRX.LowerBoundNativeComplete.native_lower`. `COMPLETE_HANDOFF_RU.md` содержит
точную область и границы относительно графового API, верхней и диаметра.
