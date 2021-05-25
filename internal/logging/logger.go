// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

// Package logging contains degitx logging API, mapping and configuring internal implementation.
// zap is current implementation
package logging

import (
	"strings"

	"go.uber.org/zap"
	"go.uber.org/zap/zapcore"
)

// LogLevel that is supported with current API
//go:generate stringer -type=LogLevel
type LogLevel int8

// Supported log levels
const (
	Debug LogLevel = iota
	Info
	Warn
	Error
)

// Logger is a struct that encapsulates logger implementation
type Logger struct {
	internalLogger        *zap.Logger
	internalSugaredLogger *zap.SugaredLogger
}

// NewLogger creates new Logger
func NewLogger(tag string) (*Logger, error) {
	internalLogger, internalSugaredLogger, err := initInternalLogger(tag)
	if err != nil {
		return nil, err
	}
	return &Logger{
			internalLogger,
			internalSugaredLogger,
		},
		nil
}

// Debug level log
func (log *Logger) Debug(template string) {
	log.internalLogger.Debug(template)
}

// Info level log
func (log *Logger) Info(template string) {
	log.internalLogger.Info(template)
}

// Warn level log
func (log *Logger) Warn(template string) {
	log.internalLogger.Warn(template)
}

// Error level log
func (log *Logger) Error(template string) {
	log.internalLogger.Error(template)
}

// Debugf Printf-like debug level log
func (log *Logger) Debugf(template string, args ...interface{}) {
	log.internalSugaredLogger.Debugf(template, args...)
}

// Infof Printf-like info level log
func (log *Logger) Infof(template string, args ...interface{}) {
	log.internalSugaredLogger.Infof(template, args...)
}

// Warnf Printf-like warn level log
func (log *Logger) Warnf(template string, args ...interface{}) {
	log.internalSugaredLogger.Warnf(template, args...)
}

// Errorf Printf-like error level log
func (log *Logger) Errorf(template string, args ...interface{}) {
	log.internalSugaredLogger.Errorf(template, args...)
}

func initInternalLogger(tag string) (*zap.Logger, *zap.SugaredLogger, error) {
	spec := []zapcore.Field{
		zap.String("tag", tag),
	}
	if len(logCtx.nodeID) != 0 {
		spec = append(spec, zap.String("locator", logCtx.nodeID))
	}

	cores := []zapcore.Core{}
	closeOuts := []func(){}
	for idx, out := range logCtx.cfg.Outputs {
		sink, closeOut, err := openSinks(out.Path)
		if err != nil {
			return nil, nil, err
		}
		closeOuts = append(closeOuts, closeOut)
		encoder := *logCtx.plain
		if strings.EqualFold(out.Format, "json") {
			encoder = *logCtx.json
		}
		cores = append(cores, zapcore.NewCore(encoder, sink, logCtx.registeredLevel[idx]).With(spec))
	}
	errSinks, err := openErrorSinks(logCtx.cfg.ErrorsOut, closeOuts)
	if err != nil {
		return nil, nil, err
	}
	core := zapcore.NewTee(cores...)
	logger := zap.New(
		core,
		zap.ErrorOutput(errSinks),
	)
	defer logger.Sync() //nolint:errcheck // zap docs says it normal way to use Sync()
	sugared := logger.Sugar()
	return logger, sugared, nil
}
